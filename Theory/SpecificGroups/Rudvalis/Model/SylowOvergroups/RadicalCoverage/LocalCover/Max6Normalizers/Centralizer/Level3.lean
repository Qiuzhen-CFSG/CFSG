module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max6Normalizers.Centralizer.Level3Step10
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Rigidity.Level5

/-!
# Centralizer point-image bound after 3 fixed points

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

private theorem decodeFixed3 : ∀ x : Fin 4060,
    c3s10 x = c3s10 3 → x = 3 := by
  apply Rudvalis.Data.allFin
  decide +kernel

private theorem decodeFixed4 : ∀ x : Fin 4060,
    c3s10 x = c3s10 4 → x = 4 := by
  apply Rudvalis.Data.allFin
  decide +kernel

/-- Three fixed points suffice for a relation automorphism commuting with z. -/
public theorem fix_three_eq_one (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ relationAut)
    (hz : ∀ x, p (AlignmentData.involutionPerm x) = AlignmentData.involutionPerm (p x))
    (hf : ∀ x : Fin 4060, x.val < 3 → p x = x) : p = 1 := by
  apply fix_five_eq_one p hp
  intro x hx
  by_cases h3 : x.val < 3
  · exact hf x h3
  · have h : x = 3 ∨ x = 4 := by
      have h : x.val = 3 ∨ x.val = 4 := by omega
      rcases h with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases h with rfl | rfl
    · exact decodeFixed3 (p 3) (c3s10_preserved p hp hz hf 3)
    · exact decodeFixed4 (p 4) (c3s10_preserved p hp hz hf 4)

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.Max6Certificate.CentralizerCertificate
