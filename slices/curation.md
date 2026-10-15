# Saved real slices and cameras

Each `slices/<instance-id>.json` records the phase choices, orthonormal real four-plane, mesh, and camera used to visualize that instance. These settings must agree with `instance.rec` and the mesh manifest. The projected box is fixed at ±10, and x-ray reach is 2.0.

Meshes sample the real section obtained by intersecting the chosen four-plane with the unit sphere and the sextic, then stereographically projecting into three dimensions. Their positions and normals are floating-point presentation data. They do not prove smoothness, topology, or certificate validity.

`validation.json` records finite-value, normal, coordinate-bound, index-bound, edge-length, and root-residual checks. A finite grid can miss sufficiently thin features. Camera and slice choices are aesthetic decisions, independent of the mathematical target.

Accepted denominator values are evaluated from the accepted record when the mesh is loaded. Open instances contain no saved denominator samples. Changing a solution therefore does not require changing the geometric mesh.

The home page has a separate saved Contact cone 46006 view: the 256³ mesh, seed 245646, yaw 0.710, pitch 0.455, and distance 3.22 described in `home.json`. Preserve it independently of the atlas card's camera and mesh.
