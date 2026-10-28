module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.Centralizer.Level2Step10
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.Centralizer.Orbit2

/-!
# Centralizer point-image bound after 2 fixed points

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

private theorem decode2 : ∀ x : Fin 4060,
    c2s10 x = c2s10 2 → point2 (pointInv2 x) = x := by
  apply Rudvalis.Data.allFin
  decide +kernel

public theorem image2_mem_range (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ relationAut)
    (hz : ∀ x, p (AlignmentData.involutionPerm x) = AlignmentData.involutionPerm (p x))
    (hf : ∀ x : Fin 4060, x.val < 2 → p x = x) :
    p 2 ∈ Set.range point2 :=
  ⟨pointInv2 (p 2), decode2 (p 2)
    (c2s10_preserved p hp hz hf 2)⟩

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate.CentralizerCertificate
