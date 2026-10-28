module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.Assembly
public import Theory.GroupTheory.RankOneSylowExtension
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Mathlib.GroupTheory.Nilpotent

/-!
# Simple groups as top E-members

In a finite nonsolvable simple group the solvable radical is trivial, the
solvable and two-residuals are the whole group, and the radical quotient has
one normal component. Its commutator with any nontrivial subgroup is the whole
component. These facts verify every clause of E.1.2(E2), including the local
tau orbit. Both quotients in E.1.5 preserve the rank of an embedded elementary
subgroup, so a top E-member cannot occur below that rank.

This is the simple-group calculation used by the Suzuki model proof of
Aschbacher--Smith E.1.14(1), printed p.214 (PDF p.225), citing Aschbacher,
*GF(2)-representations of finite groups* (1982), Lemma 4.7. The E-member
conventions are those of E.1.1--5, printed pp.209--211.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Suzuki.ModelGeneration
variable {H : Type*} [Group H] [Finite H] [IsSimpleGroup H]

omit [Finite H] in
private theorem simple_normal_solvable_eq_bot (hH : ¬ Group.IsSolvable H)
    (R : Subgroup H) [R.Normal] [Group.IsSolvable R] : R = ⊥ := by
  rcases (inferInstance : R.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (hH (Group.isSolvable_of_surjective
      (f := ((MulEquiv.subgroupCongr h).trans topEquiv).toMonoidHom)
      ((MulEquiv.subgroupCongr h).trans topEquiv).surjective)).elim

omit [Finite H] in
private theorem simple_perfect (hH : ¬ Group.IsSolvable H) : Group.IsPerfect H := by
  refine ⟨(IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator H)
    inferInstance).resolve_left ?_⟩
  intro h
  let : IsMulCommutative H := (commutator_eq_bot_iff H).mp h
  exact hH (Group.isSolvable_of_comm (fun a b => mul_comm a b))

omit [Finite H] in
private theorem simple_center (hH : ¬ Group.IsSolvable H) : center H = ⊥ := by
  exact simple_normal_solvable_eq_bot hH _

private theorem simple_residual (hH : ¬ Group.IsSolvable H) :
    pResidual 2 H = solvableResidual H := by
  let := simple_perfect hH
  rw [solvableResidual_eq_top, pResidual_eq_top_iff]
  intro N hN hp
  let := hN
  rcases hN.eq_bot_or_eq_top with h | h
  · let e : (H ⧸ N) ≃* H :=
      (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot
    have hpH : IsPGroup 2 H := hp.of_equiv e
    let := hpH.isNilpotent
    exact (hH inferInstance).elim
  · exact h

variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial subgroup of a nonsolvable simple group satisfies the full E2
condition, including the radical quotient and the local tau orbit. -/
theorem eCaseComponent_of_simple (T A K : Subgroup G) [IsSimpleGroup K]
    (hK : ¬ Group.IsSolvable K) (hAK : A ≤ K) (hA : A ≠ ⊥) :
    ECaseComponent T A K := by
  have hR : solvableRadical K = ⊥ := simple_normal_solvable_eq_bot hK _
  let Q := K ⧸ solvableRadical K
  let e : Q ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hR).trans QuotientGroup.quotientBot
  let : IsSimpleGroup Q := e.isSimpleGroup
  have hQ : ¬ Group.IsSolvable Q := fun h => hK (by
    let := h
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  let := simple_perfect hQ
  let : IsQuasisimple Q := ⟨
    ((QuotientGroup.quotientMulEquivOfEq (simple_center hQ)).trans
      QuotientGroup.quotientBot).isSimpleGroup⟩
  let : IsQuasisimple (⊤ : Subgroup Q) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have hC : IsComponent Q (⊤ : Subgroup Q) := ⟨.top, inferInstance⟩
  have hL : componentLayer Q = ⊤ := top_unique (le_sSup hC)
  have hq : Function.Injective (QuotientGroup.mk' (solvableRadical K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hR]
  let a : Subgroup Q := (A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))
  have ha : a ≠ ⊥ := by
    intro ha
    have hab := (map_eq_bot_iff_of_injective _ hq).mp ha
    have he := congrArg (Subgroup.map K.subtype) hab
    rw [map_subgroupOf_eq_of_le hAK, Subgroup.map_bot] at he
    exact hA he
  have hc : ⁅(⊤ : Subgroup Q), a⁆ = ⊤ := by
    have hn : (⁅(⊤ : Subgroup Q), a⁆).Normal := by
      rw [← normalizer_eq_top_iff]
      exact top_unique (normalizer_commutator_ge_left ⊤ a)
    exact hn.eq_bot_or_eq_top.resolve_left (fun h => ha (le_bot_iff.mp
      ((commutator_top_left_eq_bot_iff_le_center.mp h).trans (simple_center hQ).le)))
  refine ⟨?_, ?_, simple_residual hK, ⊤, hC, ?_, Or.inl hc.symm⟩
  · rw [hR]
    let S : Sylow 2 (⊥ : Subgroup K) := Classical.choice inferInstance
    exact ⟨S, inferInstance⟩
  · change HasTwoGroupQuotient (componentLayer Q)
    rw [hL]
    refine ⟨inferInstance, ?_⟩
    intro x
    refine ⟨0, ?_⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (⊤ : Subgroup Q) x
    simp only [pow_zero, pow_one]
    exact (QuotientGroup.eq_one_iff y).mpr (mem_top y)
  · rw [ValuesEvenClassical.RankOneUpper.conjugateJoin_eq_of_normal]
    exact hL

/-- At the whole group, either rank bound retains the full rank of A. -/
theorem rank_le_of_top_member [IsSimpleGroup G] (hG : ¬ Group.IsSolvable G)
    {i : ℕ} {T A : Subgroup G} (h : IsEMemberAt i T A ⊤) : Group.rank A ≤ i := by
  let : IsSimpleGroup (⊤ : Subgroup G) := topEquiv.isSimpleGroup
  have ht : ¬ Group.IsSolvable (⊤ : Subgroup G) := fun ht => hG (by
    let := ht
    exact Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom) topEquiv.surjective)
  rcases h.2 with h | h
  · let := (pCore_isPGroup (p := 2) (G := (⊤ : Subgroup G))).isNilpotent
    have hr := h.2
    rwa [Subgroup.RankOneSylowExtension.rank_image_solvable_quotient_eq
      ⊤ A ⊤ ht le_top le_rfl] at hr
  · have hr := h.2
    rwa [Subgroup.RankOneSylowExtension.rank_image_solvable_quotient_eq
      ⊤ A ⊤ ht le_top le_rfl] at hr
end CFSG.Quasithin.ChapterE.ExceptionalValues.Suzuki.ModelGeneration
