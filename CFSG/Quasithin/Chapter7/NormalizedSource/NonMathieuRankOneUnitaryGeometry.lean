module
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Unitary
public import Theory.Representation.BinaryOffender.SylowTransport

/-!
# Near-offender exclusion for the marked unitary natural action

The natural inner elementary actors move 2s dimensions and have rank at most s.
An outer actor induces the nontrivial field involution. Its fixed-space bound
excludes ratio at most two, including s=2 where the rough rank comparison
alone is insufficient. Changing the Hermitian basis preserves the full action.

Source: Aschbacher--Smith H.2 and K.3.3, printed pp.378,456.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterK.RankOne
variable {X E F : Type*} [Group X] [Finite X]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
  {J : HermitianForm 3 F} {ρ : Representation (ZMod 2) X E} {Q : Subgroup X}

/-- The marked unitary action has no near offenders, including at s=2. -/
theorem unitary_elementary_geometry
    (h : SourceHypotheses ρ Q) (M : UnitaryModel J ρ Q)
    {s : ℕ} (hs : 2 ≤ s) (hcard : Nat.card F = (2^s)^2)
    (hconj : ∀ x : F, J.conj x = x^(2^s))
    (A : Subgroup X) (hA : IsElementaryTwo A) :
    2*s ≤ fixedCodim ρ A ∧ rank A + 1 < fixedCodim ρ A := by
  obtain ⟨M₀⟩ := M.exists_standard (by omega) hcard hconj
  let : Q.Normal := h.layer_normal
  obtain ⟨C,_⟩ := M₀.exists_semilinearControl h rfl hs hcard hconj
  have hgap : rank A + 1 < fixedCodim ρ A := by
    by_contra hn
    have hrpos := hA.rank_pos
    have hratio : actionRatio ρ A ≤ 2 :=
      (actionRatio_le_nat_iff ρ hA 2).mpr (by omega)
    have hAQ := C.elementary_le_layer rfl hs hcard hconj hA hratio
    have hr := M₀.elementary_rank_le rfl hs hcard hconj hA hAQ
    have hc := M₀.elementary_fixedCodim rfl hs hcard hconj hA hAQ
    omega
  refine ⟨?_,hgap⟩
  by_cases hAQ : A ≤ Q
  · exact (M₀.elementary_fixedCodim rfl hs hcard hconj hA hAQ).ge
  · obtain ⟨t,htA,htQ⟩ := Set.not_subset.mp hAQ
    let : IsElementaryAbelian 2 A := hA.2
    have ht : t^2 = 1 := elemPow_eq_one_of_isElementaryAbelian t htA
    have hcod := C.outer_fixedCodim hcard ht htQ
    have hle := NaturalTensor.fixedCodim_mono ρ (zpowers_le.mpr htA)
    omega
end CFSG.Quasithin.Chapter7.NormalizedSource
