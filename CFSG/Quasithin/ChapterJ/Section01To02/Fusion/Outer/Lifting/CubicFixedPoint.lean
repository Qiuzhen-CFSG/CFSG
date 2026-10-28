module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Defs
public import Theory.GroupAction.PGroupConjugationFixedPoint
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# A cubic-centralizing outer involution from the count

The literal subgroup B of L₁ acts on outer involutions by conjugation.
Relative normality of K = O²(H) preserves the set. Since 640 is prime to
three, the p-group fixed-point congruence constructs an involution in C_H(B).
This avoids any appeal to J.2.5, or any assertion that B is Sylow in H.

The count is an explicit premise here. `Outer.Lifting.involution_lifting`
discharges it using the actual Q/U and U/Z fibers in `Lifting.Count`.

Source: Aschbacher–Smith, J.2.6, printed p.435 (PDF p.446).
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer
variable {G : Type*} [Group G] [Finite G]

/-- Cubic fixed-point counting constructs the witness before J.2.5.
It uses the literal B and does not need a Sylow assertion in H. -/
theorem exists_cubic_centralizing_involution_of_count (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (hcard : Nat.card (involutionsOutside d.H d.K) = 640) :
    ∃ i : CB d B, (i : G) ∉ d.K ∧ orderOf (i : G) = 2 := by
  have hBH : BSubgroup d B ≤ d.H :=
    (map_subtype_le _).trans ((map_subtype_le _).trans inf_le_right)
  have hNK : d.H ≤ normalizer d.K := by
    have hn := le_normalizer_map (H := pResidual 2 d.H) d.H.subtype
    simpa only [TypeRuSetup.K, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hn
  have hstable : ∀ a : BSubgroup d B, ∀ x ∈ involutionsOutside d.H d.K,
      (a : G) * x * (a : G)⁻¹ ∈ involutionsOutside d.H d.K := by
    intro a x hx
    refine ⟨d.H.mul_mem (d.H.mul_mem (hBH a.property) hx.1)
      (d.H.inv_mem (hBH a.property)), ?_, ?_⟩
    · exact fun h => hx.2.1 ((mem_normalizer_iff.mp (hNK (hBH a.property)) x).mpr h)
    · exact ((MulAut.conj (a : G)).orderOf_eq x).trans hx.2.2
  obtain ⟨i, hi, hc⟩ := exists_mem_centralizer_of_conjugation_stable_set
    (BSubgroup d B) (B.isPGroup'.map d.L₁.subtype)
    (involutionsOutside d.H d.K) hstable (by rw [hcard]; decide)
  exact ⟨⟨i, hi.1, hc⟩, hi.2⟩

end CFSG.Quasithin.ChapterJ.Fusion.Outer
