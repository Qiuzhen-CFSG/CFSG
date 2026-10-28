module

public import Theory.SpecificGroups.Tits.R1WordCertificate.Context
public import Theory.SpecificGroups.Tits.R1WordCertificate.factsTable
public import Theory.SpecificGroups.Tits.R1WordCertificate.instructionsTable

/-! Generated kernel certificate; reproduce with `refs/original/n-group-global/parrott-r1-word-certificate/generate.py`.
Source: Parrott (1972), §5, p. 683; see `parrott-tits-presentation.md`. -/

public section
namespace Tits.R1WordCertificate
open Subgroup.CosetWordCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem checked_32768 : checkChunk context facts instructions 32768 4096 = true := by decide +kernel

end Tits.R1WordCertificate
