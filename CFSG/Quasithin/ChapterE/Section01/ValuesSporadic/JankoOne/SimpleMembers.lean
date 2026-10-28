module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Simple groups as whole-group E-members

A nontrivial subgroup of a nonabelian simple perfect group has full
commutator with the ambient group. The solvable radical is trivial, the
layer is the whole radical quotient, and both residuals are the whole
group. These observations verify E.1.2(E2), including its corrected local
tau orbit: the unique component is normal, so every such orbit generates it.

This supplies the proper-elementary-subgroup branch of the J₁ proof.
Source: Aschbacher--Smith, E.1.2(E2), printed p.210, applied in E.1.14(5),
printed p.214.
-/

public section
namespace CFSG.Quasithin.ChapterE.JankoOne
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem simple_radical_eq_bot {H : Type*} [Group H] [Finite H]
    [IsSimpleGroup H] [Group.IsPerfect H] : solvableRadical H = ⊥ := by
  rcases (inferInstance : (solvableRadical H).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hs : Group.IsSolvable (⊤ : Subgroup H) := h ▸ inferInstance
    let := hs
    exact (Group.IsPerfect.not_isSolvable H
      (Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup H) ≃* H).toMonoidHom) topEquiv.surjective)).elim

private theorem simple_center_eq_bot {H : Type*} [Group H]
    [IsSimpleGroup H] [Group.IsPerfect H] : center H = ⊥ := by
  rcases (inferInstance : (center H).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative H (center_eq_top_iff.mp h)).elim

private theorem simple_commutator_top {H : Type*} [Group H]
    [IsSimpleGroup H] [Group.IsPerfect H] (A : Subgroup H) (hA : A ≠ ⊥) :
    ⁅(⊤ : Subgroup H), A⁆ = ⊤ := by
  have hn : (⁅(⊤ : Subgroup H), A⁆).Normal :=
    normalizer_eq_top_iff.mp (top_le_iff.mp (normalizer_commutator_ge_left ⊤ A))
  rcases hn.eq_bot_or_eq_top with h | h
  · exact (hA (le_bot_iff.mp ((commutator_top_left_eq_bot_iff_le_center.mp h).trans
      simple_center_eq_bot.le))).elim
  · exact h

private theorem perfect_two_residual {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] : pResidual 2 H = ⊤ := by
  apply (pResidual_eq_top_iff 2 H).mpr
  intro N hN hp
  let := hN
  by_contra hne
  let : Nontrivial (H ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (H ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (H ⧸ N) := hp.isNilpotent
  exact Group.IsPerfect.not_isSolvable (H ⧸ N) inferInstance

/-- The whole nonabelian simple group satisfies E2 for every nontrivial A. -/
theorem top_component [IsSimpleGroup G] [Group.IsPerfect G]
    (T A : Subgroup G) (hA : A ≠ ⊥) : ECaseComponent T A ⊤ := by
  let K : Subgroup G := ⊤
  let : IsSimpleGroup K := topEquiv.isSimpleGroup
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := (topEquiv : K ≃* G).symm.toMonoidHom) topEquiv.symm.surjective
  have hR : solvableRadical K = ⊥ := simple_radical_eq_bot
  let Q := K ⧸ solvableRadical K
  let e : Q ≃* K := (QuotientGroup.quotientMulEquivOfEq hR).trans QuotientGroup.quotientBot
  let : IsSimpleGroup Q := e.isSimpleGroup
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hz : center Q = ⊥ := simple_center_eq_bot
  let : IsQuasisimple Q := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  let : IsQuasisimple (⊤ : Subgroup Q) :=
    IsQuasisimple.of_mulEquiv topEquiv.symm
  have hcomp : IsComponent Q ⊤ := ⟨(inferInstance : (⊤ : Subgroup Q).Normal).isSubnormal,
    inferInstance⟩
  have hE : componentLayer Q = ⊤ := top_unique (le_sSup hcomp)
  have ha : (A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K)) ≠ ⊥ := by
    intro ha
    have hinj : Function.Injective (QuotientGroup.mk' (solvableRadical K)) :=
      (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hR])
    have hab : A.subgroupOf K = ⊥ := (map_eq_bot_iff_of_injective _ hinj).mp ha
    apply hA
    have hm := congrArg (map K.subtype) hab
    simpa [K] using hm
  refine ⟨?_, ?_, ?_, ⊤, hcomp, ?_, Or.inl (simple_commutator_top _ ha).symm⟩
  · unfold IsTwoClosed
    rw [hR]
    exact ⟨default, inferInstance⟩
  · change HasTwoGroupQuotient (componentLayer Q)
    rw [hE]
    let : Subsingleton (Q ⧸ (⊤ : Subgroup Q)) := QuotientGroup.subsingleton_quotient_top
    exact ⟨inferInstance, IsPGroup.of_subsingleton 2 _⟩
  · change pResidual 2 K = solvableResidual K
    rw [perfect_two_residual, solvableResidual_eq_top]
  · change componentLayer Q = conjugateJoin _ ⊤
    simp [hE, conjugateJoin]

end CFSG.Quasithin.ChapterE.JankoOne
