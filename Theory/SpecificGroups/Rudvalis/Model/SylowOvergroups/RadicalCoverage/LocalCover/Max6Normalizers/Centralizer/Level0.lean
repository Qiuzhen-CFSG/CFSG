module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.Centralizer.Basic
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.Centralizer.Orbit0

/-!
# Centralizer point-image bound after 0 fixed points

The ATLAS inverse-action words and the certified Rudvalis orbital are unchanged.
These generated witnesses are untrusted until their Lean kernel checks pass.
Source: RuG1-max6W1 and degree-4060 permutations, attributed in
SylowOvergroups.Definitions and Model.PermutationData; GLS3 Table 5.3r,
and [Asc86b] as cited on quasithin printed p.511.
See Centralizer/source/Generate.py for witness generation.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate.CentralizerCertificate
open Rudvalis.OuterNormalizer
open Rudvalis.OuterNormalizer.InvarianceCertificate
open Rudvalis.OuterNormalizer.RigidityCertificate

set_option maxRecDepth 30000
set_option Elab.async false

private theorem decode0 : ∀ x : Fin 4060,
    (seed 0) x = (seed 0) 0 → point0 (pointInv0 x) = x := by
  apply Rudvalis.Data.allFin
  decide +kernel

public theorem image0_mem_range (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ relationAut)
    (hz : ∀ x, p (AlignmentData.involutionPerm x) = AlignmentData.involutionPerm (p x))
    (hf : ∀ x : Fin 4060, x.val < 0 → p x = x) :
    p 0 ∈ Set.range point0 :=
  ⟨pointInv0 (p 0), decode0 (p 0)
    (seed_preserved 0 p hp hz hf 0)⟩

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate.CentralizerCertificate
