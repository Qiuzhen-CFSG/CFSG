module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.Centralizer.Level1Step04
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.Centralizer.Orbit1

/-!
# Centralizer point-image bound after 1 fixed points

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

private theorem decode1 : ∀ x : Fin 4060,
    c1s4 x = c1s4 1 → point1 (pointInv1 x) = x := by
  apply Rudvalis.Data.allFin
  decide +kernel

public theorem image1_mem_range (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ relationAut)
    (hz : ∀ x, p (AlignmentData.involutionPerm x) = AlignmentData.involutionPerm (p x))
    (hf : ∀ x : Fin 4060, x.val < 1 → p x = x) :
    p 1 ∈ Set.range point1 :=
  ⟨pointInv1 (p 1), decode1 (p 1)
    (c1s4_preserved p hp hz hf 1)⟩

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate.CentralizerCertificate
