module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.ResidualCore
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.OddThree
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.FactorPosition.SylowModel
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.Projective

/-!
# Excluding the odd ternary classical source rows

Odd-characteristic linear and unitary groups in dimension three have
two-rank at most two and cyclic Sylow centers. For the full special groups,
the odd scalar kernel induces an isomorphism on Sylow two-subgroups;
we retain the full group and transport only this Sylow fact.

The original moved-component action now kills the two-core of the residual
image. This gives a literal PSL₂(2ⁿ), normalized by the full quotient Sylow.
The established odd-ternary Sylow-action obstruction excludes it. Thus
both the projective rows and the full cubic central covers are eliminated.

Source: Aschbacher--Smith, A.3.6 and 3.3.12, printed p.589, used in
3.3.16, pp.590--591. Recognition is assembled by the same line-action owner.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}

open Chapter1.Section02 Chapter1.Section02.LocalModels
open scoped MatrixGroups

private theorem odd_three_center_cyclic {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign Q u 3 p ∨ IsSLSign Q u 3 p) (P : Sylow 2 Q) :
    IsCyclic (center P) := by
  let : Fact p.Prime := ⟨hp⟩
  cases u with
  | false =>
    rcases hm with hm | hm
    · exact Chapter1.XiEmbedding.InvariantLarge.OddCartan.isPSL_sylow_center_cyclic ho hm P
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
      let q := Matrix.PSL3.projection F
      let U := P'.mapSurjective (Matrix.PSL3.projection_surjective F)
      have hk : Nat.Coprime 2 (Nat.card q.ker) := by
        rw [Matrix.PSL3.projection_ker]
        exact Nat.coprime_two_left.mpr (Matrix.SL3.odd_card_center F)
      let a : P ≃* U := (e.subgroupMap (P : Subgroup Q)).trans
        (Sylow.equivOfSurjectiveCoprime q (Matrix.PSL3.projection_surjective F) hk P' U)
      let : IsCyclic (center U) :=
        Chapter1.XiEmbedding.InvariantLarge.OddCartan.isPSL_sylow_center_cyclic ho
          ⟨F,inferInstance,inferInstance,hF,⟨MulEquiv.refl _⟩⟩ U
      exact isCyclic_of_injective (centerCongr a).toMonoidHom (centerCongr a).injective
  | true =>
    rcases hm with hm | hm
    · exact Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition.isPSU_sylow_center_cyclic p ho hm P
    · obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
      let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
      let q := J.specialToProjective
      let U := P'.mapSurjective J.specialToProjective_surjective
      have hk : Nat.Coprime 2 (Nat.card q.ker) :=
        Nat.coprime_two_left.mpr J.odd_card_specialToProjective_ker
      let a : P ≃* U := (e.subgroupMap (P : Subgroup Q)).trans
        (Sylow.equivOfSurjectiveCoprime q J.specialToProjective_surjective hk P' U)
      let : IsCyclic (center U) :=
        Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition.isPSU_sylow_center_cyclic p ho
          ⟨F,inferInstance,inferInstance,J,hF,hconj,⟨MulEquiv.refl _⟩⟩ U
      exact isCyclic_of_injective (centerCongr a).toMonoidHom (centerCongr a).injective

private theorem odd_three_rank {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool)
    (hm : IsPSLSign Q u 3 p ∨ IsSLSign Q u 3 p) : primeRank 2 Q ≤ 2 := by
  open Theory.SpecificGroups.OddThreeRank in
    cases u with
    | false =>
      rcases hm with hm | hm
      · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
        rw [primeRank_equiv 2 e]
        exact psl3_primeRank_two_le hp ho hF
      · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
        exact special_primeRank_two_le e
          (two_ne_zero_of_odd_card ho (k := 1) (by simpa using hF))
    | true =>
      rcases hm with hm | hm
      · obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
        rw [primeRank_equiv 2 e]
        exact psu3_primeRank_two_le J hp ho hF hconj
      · obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
        rw [primeRank_equiv 2 e]
        exact hermitian_special_primeRank_two_le J (two_ne_zero_of_odd_card ho hF)

namespace MovedComponent
variable (E : MovedComponent S f A)

/-- Neither an odd projective ternary group nor its full special cover can
be the actual moved-component quotient. -/
theorem quotient_not_odd_classical {p : ℕ} (hp : p.Prime) (ho : Odd p) (u : Bool) :
    ¬ IsPSLSign (E.component ⧸ pCore 2 E.component) u 3 p ∧
      ¬ IsSLSign (E.component ⧸ pCore 2 E.component) u 3 p := by
  have hfalse (hm : IsPSLSign (E.component ⧸ pCore 2 E.component) u 3 p ∨
      IsSLSign (E.component ⧸ pCore 2 E.component) u 3 p) : False := by
    obtain ⟨P,hP⟩ := E.quotientSylow_isSylow
    have hc : IsCyclic (center E.quotientSylow) := hP ▸ odd_three_center_cyclic hp ho u hm P
    have hb := E.residualImage_isPSL_of_core_eq_bot
      (E.residualImage_core_eq_bot_of_cyclic_center (odd_three_rank hp ho u hm) hc)
    let : Group.IsPerfect E.residualImage := by
      let := E.residualImage_local.perfect
      exact Group.IsPerfect.ofSurjective
        (f := (subgroupOfEquivOfLe (show E.residualImage ≤ E.residualImage ⊔ E.quotientSylow from le_sup_left)).toMonoidHom)
        (subgroupOfEquivOfLe le_sup_left).surjective
    have hnot := ChapterC.Section05.NormalizerControl.EmbeddingSelection.not_odd_three_binary_intrinsic
      P E.residualImage (by have := S.nonbinary; omega) hb
      (hP.symm ▸ E.quotientSylow_normalizes_residualImage) hp ho u
    exact hm.elim hnot.1 hnot.2
  exact ⟨fun h => hfalse (.inl h),fun h => hfalse (.inr h)⟩

end MovedComponent
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
