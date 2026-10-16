/* Page-side controls and watchdog. Never create a WebGL context on this thread. */
(() => {
  'use strict';
  const workerURL = new URL('surface-worker.js', document.currentScript.src);
  const TIMEOUT = 5000;
  function create(canvas, {onStatus = () => {}, onModeChange = () => {}} = {}) {
    let worker = null, stopped = false, mode = 'parallax', meta = null, camera = null;
    let lastPulse = performance.now(), watchdog;
    const listeners = [];
    const listen = (target, name, callback, options) => {
      target.addEventListener(name, callback, options);
      listeners.push(() => target.removeEventListener(name, callback, options));
    };
    const send = message => { if (!stopped && worker) worker.postMessage(message); };
    const size = () => ({width:canvas.clientWidth, height:canvas.clientHeight,
      innerWidth, innerHeight, devicePixelRatio:devicePixelRatio || 1});
    function stop(message) {
      if (stopped) return;
      stopped = true;
      clearInterval(watchdog);
      worker?.terminate(); worker = null;
      listeners.forEach(remove => remove());
      // Detach the transferred drawing surface; no stale GPU image or handles
      // survive a failure. Keep the element so the rest of the page can use it.
      const blank = canvas.cloneNode(false);
      blank.classList.remove('free-camera'); blank.style.touchAction = 'auto';
      canvas.replaceWith(blank);
      if (message) {
        console.warn('Surface paused:', message);
        onStatus({state:'error', message});
      }
    }
    function setMode(value) {
      mode = value === 'free' ? 'free' : 'parallax';
      if (!stopped) {
        canvas.classList.toggle('free-camera', mode === 'free');
        canvas.style.touchAction = mode === 'free' ? 'none' : 'auto';
        send({type:'mode', mode});
      }
      onModeChange(mode);
    }
    const api = {
      async setCase(record) {
        if (stopped) return;
        onStatus({state:'loading', message:'Preparing the saved slice…'});
        // Only presentation data crosses the worker boundary, not the proof/text.
        send({type:'case', record:{id:record.id, title:record.title, render:record.render,
          certificateAvailable:record.certificateAvailable, evidenceKind:record.evidenceKind, status:record.status}});
      },
      setMode, resetCamera:() => send({type:'reset'}), getMode:() => mode,
      getMeta:() => meta, getCamera:() => camera, destroy:() => stop()
    };
    // Older browsers keep the atlas usable instead of falling back to blocking GL.
    if (typeof Worker === 'undefined' || !canvas.transferControlToOffscreen) {
      stop('This browser cannot run the 3D view separately from the page.');
      return api;
    }
    try {
      worker = new Worker(workerURL);
      worker.onmessage = ({data}) => {
        if (stopped) return;
        lastPulse = performance.now();
        if (data.type === 'fatal') { stop(data.value); return; }
        if (data.type === 'status') {
          if (data.value.meta) meta = data.value.meta;
          onStatus(data.value);
        } else if (data.type === 'mode' && mode !== data.value) {
          mode = data.value;
          canvas.classList.toggle('free-camera', mode === 'free');
          canvas.style.touchAction = mode === 'free' ? 'none' : 'auto';
          onModeChange(mode);
        } else if (data.type === 'label') canvas.setAttribute('aria-label', data.value);
        else if (data.type === 'pulse' && data.value) camera = data.value;
      };
      worker.onerror = event => { event.preventDefault(); stop(event.message || 'The 3D view could not start.'); };
      worker.onmessageerror = () => stop('The 3D view could not communicate with the page.');
      const offscreen = canvas.transferControlToOffscreen();
      worker.postMessage({type:'init', canvas:offscreen, size:size(), hidden:document.hidden,
        reducedMotion:matchMedia('(prefers-reduced-motion: reduce)').matches}, [offscreen]);
      watchdog = setInterval(() => {
        if (!document.hidden && performance.now() - lastPulse > TIMEOUT)
          stop('The 3D view stopped responding and has been paused to keep the page usable.');
      }, 500);
      listen(window, 'resize', () => send({type:'size', size:size()}), {passive:true});
      listen(document, 'visibilitychange', () => {
        // Browser timer throttling / laptop sleep is not a renderer failure.
        lastPulse = performance.now(); send({type:'visibility', hidden:document.hidden});
      });
      const keys = ['pointerId','pointerType','clientX','clientY','button','deltaY','key','shiftKey','altKey','ctrlKey','metaKey'];
      function input(target, name, event) {
        const properties = {};
        for (const key of keys) if (event[key] !== undefined) properties[key] = event[key];
        if (name === 'keydown') properties.textInput = !!event.target?.closest?.('input,textarea,select,[contenteditable="true"]');
        send({type:'input', target, name, properties});
      }
      for (const name of ['pointermove','pointerleave','blur','keydown'])
        listen(window, name, event => input('view', name, event), {passive:true});
      for (const name of ['contextmenu','dblclick','wheel','pointerdown','pointermove','pointerup','pointercancel','lostpointercapture'])
        listen(canvas, name, event => {
          if (mode !== 'free') return;
          if (event.cancelable) event.preventDefault();
          if (name === 'pointerdown') canvas.setPointerCapture?.(event.pointerId);
          input('canvas', name, event);
          if (name === 'pointerup' || name === 'pointercancel') {
            try { canvas.releasePointerCapture?.(event.pointerId); } catch (_) {}
          }
        }, {passive:false});
    } catch (error) { stop(error.message || 'The 3D view could not start.'); }
    return api;
  }
  window.HodgeRenderer = Object.freeze({create});
})();
