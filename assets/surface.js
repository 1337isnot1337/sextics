/* Page-side controls and watchdog. Never create a WebGL context on this thread. */
(() => {
  'use strict';
  const workerURL = new URL('surface-worker.js', document.currentScript.src);
  const TIMEOUT = 5000;
  function create(canvas, {onStatus = () => {}, onModeChange = () => {}} = {}) {
    let worker = null, failed = false, destroyed = false, mode = 'parallax', meta = null, camera = null, record = null;
    let lastPulse = performance.now(), lastTick = lastPulse, watchdog;
    let wasHidden = document.hidden, recoveryAllowed = false, recoveryPending = false, resumeUntil = 0;
    const listeners = [], canvasListeners = [];
    const listen = (target, name, callback, options, removers = listeners) => {
      target.addEventListener(name, callback, options);
      removers.push(() => target.removeEventListener(name, callback, options));
    };
    const send = message => { if (!destroyed && worker) worker.postMessage(message); };
    const size = () => ({width:canvas.clientWidth, height:canvas.clientHeight,
      innerWidth, innerHeight, devicePixelRatio:devicePixelRatio || 1});
    function release() {
      clearInterval(watchdog);
      worker?.terminate(); worker = null;
      canvasListeners.splice(0).forEach(remove => remove());
      // A new worker receives a new drawing surface. Never reuse GPU handles
      // from a lost context, even if the browser later restores that context.
      const blank = canvas.cloneNode(false);
      blank.classList.remove('free-camera'); blank.style.touchAction = 'auto';
      canvas.replaceWith(blank); canvas = blank;
      meta = null; camera = null;
    }
    function stop(message, recoverable = true) {
      if (failed || destroyed) return;
      const recovering = recoverable && recoveryAllowed &&
        (document.hidden || wasHidden || performance.now() < resumeUntil);
      release(); recoveryAllowed = false;
      if (recovering) {
        recoveryPending = true;
        onStatus({state:'loading', message:'Restoring the saved slice…'});
        if (!document.hidden) start();
        return;
      }
      failed = true; recoveryPending = false;
      console.warn('Surface paused:', message);
      onStatus({state:'error', message});
    }
    function setMode(value) {
      mode = value === 'free' ? 'free' : 'parallax';
      if (!failed && !destroyed && worker) {
        canvas.classList.toggle('free-camera', mode === 'free');
        canvas.style.touchAction = mode === 'free' ? 'none' : 'auto';
        send({type:'mode', mode});
      }
      onModeChange(mode);
    }
    const api = {
      async setCase(selected) {
        if (failed || destroyed) return;
        // Only presentation data crosses the worker boundary, not the proof/text.
        record = {id:selected.id, title:selected.title, render:selected.render,
          certificateAvailable:selected.certificateAvailable, evidenceKind:selected.evidenceKind, status:selected.status};
        meta = null; camera = null;
        onStatus({state:'loading', message:'Preparing the saved slice…'});
        send({type:'case', record});
      },
      setMode, resetCamera:() => send({type:'reset'}), getMode:() => mode,
      getMeta:() => meta, getCamera:() => camera,
      destroy() { if (destroyed) return; destroyed = true; release(); listeners.splice(0).forEach(remove => remove()); }
    };
    // Older browsers keep the atlas usable instead of falling back to blocking GL.
    if (typeof Worker === 'undefined' || !canvas.transferControlToOffscreen) {
      stop('This browser cannot run the 3D view separately from the page.', false);
      return api;
    }
    const keys = ['pointerId','pointerType','clientX','clientY','button','deltaY','key','shiftKey','altKey','ctrlKey','metaKey'];
    function input(target, name, event) {
      const properties = {};
      for (const key of keys) if (event[key] !== undefined) properties[key] = event[key];
      if (name === 'keydown') properties.textInput = !!event.target?.closest?.('input,textarea,select,[contenteditable="true"]');
      send({type:'input', target, name, properties});
    }
    function start() {
      if (destroyed || failed || worker) return;
      recoveryPending = false;
      lastPulse = lastTick = performance.now();
      try {
        const current = new Worker(workerURL); worker = current;
        current.onmessage = ({data}) => {
          if (worker !== current || destroyed) return;
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
        current.onerror = event => { event.preventDefault(); if (worker === current) stop(event.message || 'The 3D view could not start.'); };
        current.onmessageerror = () => { if (worker === current) stop('The 3D view could not communicate with the page.'); };
        const offscreen = canvas.transferControlToOffscreen();
        current.postMessage({type:'init', canvas:offscreen, size:size(), hidden:document.hidden,
          reducedMotion:matchMedia('(prefers-reduced-motion: reduce)').matches}, [offscreen]);
        if (record) send({type:'case', record});
        canvas.classList.toggle('free-camera', mode === 'free');
        canvas.style.touchAction = mode === 'free' ? 'none' : 'auto';
        send({type:'mode', mode});
        watchdog = setInterval(() => {
          const now = performance.now(), delayed = now - lastTick > TIMEOUT;
          lastTick = now;
          if (document.hidden) return;
          // A suspended page may run a queued timer before visibilitychange.
          // Give it a fresh deadline; a continuously blocked worker still times out.
          if (delayed) { lastPulse = now; send({type:'visibility', hidden:false}); return; }
          if (now - lastPulse > TIMEOUT)
            stop('The 3D view stopped responding and has been paused to keep the page usable.');
        }, 500);
        for (const name of ['contextmenu','dblclick','wheel','pointerdown','pointermove','pointerup','pointercancel','lostpointercapture'])
          listen(canvas, name, event => {
            if (mode !== 'free') return;
            if (event.cancelable) event.preventDefault();
            if (name === 'pointerdown') canvas.setPointerCapture?.(event.pointerId);
            input('canvas', name, event);
            if (name === 'pointerup' || name === 'pointercancel') {
              try { canvas.releasePointerCapture?.(event.pointerId); } catch (_) {}
            }
          }, {passive:false}, canvasListeners);
      } catch (error) { stop(error.message || 'The 3D view could not start.', false); }
    }
    listen(window, 'resize', () => send({type:'size', size:size()}), {passive:true});
    listen(document, 'visibilitychange', () => {
      const hidden = document.hidden, returning = wasHidden && !hidden;
      if (hidden && !wasHidden && !failed) recoveryAllowed = true;
      // Include the watchdog's next tick after the five-second deadline.
      if (returning) resumeUntil = performance.now() + TIMEOUT + 1000;
      wasHidden = hidden;
      lastPulse = lastTick = performance.now();
      if (returning && recoveryPending) start();
      else send({type:'visibility', hidden});
    });
    for (const name of ['pointermove','pointerleave','blur','keydown'])
      listen(window, name, event => input('view', name, event), {passive:true});
    // An initially backgrounded tab need not allocate GPU resources yet.
    if (document.hidden) recoveryPending = true;
    else start();
    return api;
  }
  window.HodgeRenderer = Object.freeze({create});
})();
