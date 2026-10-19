import Proposal.GenericSpecialization
namespace GenericSpecialization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem source_inverse : sourceMinor * sourceInverse = 1 := by
  decide +kernel

end GenericSpecialization
