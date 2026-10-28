module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Actions
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.Basic
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Size and faithful full action of the original chosen module

The nontrivial perfect action of L/O₂(L) cannot act on at most four vectors:
its permutation image would be perfect and solvable. Thus the original chosen
V has order greater than four, independently of the seven-module classification.

The action of the whole join LT on the unchanged V has its literal conjugation
formula. Its kernel is C_LT(V). Reducedness from the structural prefix of
12.2.2 therefore kills the two-core of its faithful image, both in the units of
the endomorphism ring and in GL(V). This establishes the extra hypothesis of
the corrected G.3.1 recognition theorem for the whole actor used in 12.2.20;
it does not pass reducedness to an arbitrary restricted subgroup.

Source: Aschbacher--Smith, 12.2.2(3), 12.2.18 and 12.2.20, printed pp.795,801--802.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- A nontrivial perfect chosen action excludes modules of order at most four. -/
theorem chosen_card_gt_four (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) : 4 < Nat.card V := by
  classical
  by_contra! hsmall
  let := h.quasisimple
  have hcard : Nat.card D.space = Nat.card V := Nat.card_congr D.spaceEquiv.toEquiv
  let : Fintype D.space := Fintype.ofFinite _
  let e : D.space ↪ Fin 4 := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_fin, hcard] using hsmall))
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm D.space) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  let f : (L ⧸ pCore 2 L) →* Equiv.Perm D.space :=
    (MulAction.toPermHom (Module.End (ZMod 2) D.space)ˣ D.space).comp D.quotientAction.asGroupHom
  let := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  have hf (l : L) (v : D.space) : D.chosenAction l v = v := by
    have he : f (QuotientGroup.mk' (pCore 2 L) l) = 1 := congrArg Subtype.val
      (Subsingleton.elim (f.rangeRestrict (QuotientGroup.mk' (pCore 2 L) l)) 1)
    exact congrArg (fun z : Equiv.Perm D.space => z v) he
  apply D.centralAction_ne_one
  apply MonoidHom.ext
  intro l
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ v =>
    change Submodule.Quotient.mk (D.chosenAction l v) = Submodule.Quotient.mk v
    rw [hf]

/-- Conjugation by the literal join L ∨ T on the original V. -/
def chosenJoinConjugation (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    (L ⊔ (T : Subgroup G) : Subgroup G) →* MulAut V :=
  V.normalizerMonoidHom.comp (Subgroup.inclusion (sup_le D.normalizes hT))

/-- The binary representation of the whole join, before taking its image. -/
def chosenJoinAction (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    letI := D.elementary
    Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) (Additive V) := by
  letI := D.elementary
  exact Representation.elementaryRepresentation (chosenJoinConjugation D hT)

omit [Finite G] in
theorem chosenJoinAction_apply (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V) :
    letI := D.elementary
    ((chosenJoinAction D hT x (Additive.ofMul v)).toMul : G) =
      (x : G) * (v : G) * (x : G)⁻¹ := rfl

omit [Finite G] in
/-- The intrinsic centralizer is precisely the full action kernel. -/
theorem chosenJoinAction_ker (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    letI := D.elementary
    (chosenJoinAction D hT).asGroupHom.ker =
      centralizer (V.subgroupOf (L ⊔ (T : Subgroup G)) : Set (L ⊔ (T : Subgroup G) : Subgroup G)) := by
  let := D.elementary
  have hVJ : V ≤ L ⊔ (T : Subgroup G) := D.le_sylow.trans le_sup_right
  ext x
  constructor
  · intro hx v hv
    have he := congrArg (fun e : (Module.End (ZMod 2) (Additive V))ˣ =>
      (((e : Module.End (ZMod 2) (Additive V)) (Additive.ofMul ⟨(v : G), hv⟩)).toMul : G)) hx
    change (x : G) * (v : G) * (x : G)⁻¹ = (v : G) at he
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hx
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change (x : G) * (v.toMul : G) * (x : G)⁻¹ = (v.toMul : G)
    have he := congrArg (fun z : (L ⊔ (T : Subgroup G) : Subgroup G) => (z : G))
      (hx ⟨(v.toMul : G), hVJ v.toMul.property⟩ v.toMul.property)
    exact mul_inv_eq_iff_eq_mul.mpr he.symm

/-- Reducedness applies to the full faithful action, with no irreducibility input. -/
theorem chosenJoinAction_twoCore_eq_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) :
    letI := D.elementary
    pCore 2 (chosenJoinAction D (((structural G T L h).2.2 V D).1)).asGroupHom.range = ⊥ := by
  let := D.elementary
  let J := L ⊔ (T : Subgroup G)
  let W := V.subgroupOf J
  have hr : IsPReduced 2 W := ((structural G T L h).2.2 V D).2.1
  let := hr.normal
  let a := (chosenJoinAction D (((structural G T L h).2.2 V D).1)).asGroupHom
  let e : (J ⧸ centralizer (W : Set J)) ≃* a.range :=
    (QuotientGroup.quotientMulEquivOfEq (chosenJoinAction_ker D _).symm).trans
      (QuotientGroup.quotientKerEquivRange a)
  have he := pCore_map_iso 2 e
  rw [hr.quotient_pCore_eq_bot, Subgroup.map_bot] at he
  exact he.symm

/-- The same literal action in the linear-equivalence convention of G.3.1. -/
def chosenJoinLinearAction (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    letI := D.elementary
    (L ⊔ (T : Subgroup G) : Subgroup G) →*
      (Additive V ≃ₗ[ZMod 2] Additive V) := by
  letI := D.elementary
  exact (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive V)).toMonoidHom.comp
    (chosenJoinAction D hT).asGroupHom

omit [Finite G] in
theorem chosenJoinLinearAction_apply (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V) :
    letI := D.elementary
    ((chosenJoinLinearAction D hT x (Additive.ofMul v)).toMul : G) =
      (x : G) * (v : G) * (x : G)⁻¹ := rfl

/-- The actual GL-image satisfies the guard in corrected G.3.1. -/
theorem chosenJoinLinearAction_twoCore_eq_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) :
    letI := D.elementary
    pCore 2 (chosenJoinLinearAction D (((structural G T L h).2.2 V D).1)).range = ⊥ := by
  let := D.elementary
  let a := (chosenJoinAction D (((structural G T L h).2.2 V D).1)).asGroupHom
  let b := chosenJoinLinearAction D (((structural G T L h).2.2 V D).1)
  have hk : a.ker = b.ker := by
    ext x
    exact (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive V)).map_eq_one_iff.symm
  let e : a.range ≃* b.range := (QuotientGroup.quotientKerEquivRange a).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans (QuotientGroup.quotientKerEquivRange b))
  have he := pCore_map_iso 2 e
  rw [chosenJoinAction_twoCore_eq_bot h D structural, Subgroup.map_bot] at he
  exact he.symm

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
