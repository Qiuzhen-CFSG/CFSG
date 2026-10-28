module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.CentralQuotientFive
public import Theory.Representation.Quotient
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Faithful central actions of original simple-quotient choices

The original chosen Irr⁺ section has irreducible central quotient and full
commutator generation. Its two-core acts trivially; its whole actor cannot
act trivially on the central quotient, because then every commutator would
be fixed. Simplicity therefore makes the induced quotient action faithful.
In particular the actual centralizer of the chosen subgroup is its component's
two-core before any representation model is classified.

The A₅ specializations keep the supplied quotient marking and its original
conjugation action. They prepare the action required in 12.2.2(3d) and
13.3.2(3); they do not identify it with the alternating natural module.
Source: Aschbacher--Smith, A.1.40, 12.2.2 and 13.3.2, pp.31,795,885.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal two-core acts trivially on the chosen central quotient. -/
theorem centralAction_core : pCore 2 L ≤ D.chosenCentralAction.ker := by
  intro l hl
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change Submodule.Quotient.mk (D.chosenAction l v) = Submodule.Quotient.mk v
    rw [show D.chosenAction l = 1 from D.chosenAction_core hl]
    rfl

omit [Finite G] in
/-- Full commutator generation excludes a trivial action on the central quotient. -/
theorem centralAction_ne_one : D.chosenCentralAction ≠ 1 := by
  intro he
  apply D.irrPlus.isIrrPlus.not_le_fixedSpace _
  rw [← D.irrPlus.isIrrPlus.choose_spec.1]
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, v, hv, rfl⟩
  let l' : L := ⟨l, hl⟩
  let v' : D.space := ⟨v, hv⟩
  have hh := LinearMap.congr_fun (DFunLike.congr_fun he l')
    (Submodule.Quotient.mk v' : D.chosenCentralQuotient)
  change Submodule.Quotient.mk (D.chosenAction l' v') =
    (Submodule.Quotient.mk v' : D.chosenCentralQuotient) at hh
  have hz : D.chosenAction l' v' - v' ∈
      (fixedSpace (reducedRepresentation (L ⊔ (T : Subgroup G)))
        (L.subgroupOf (L ⊔ (T : Subgroup G)))).comap D.space.subtype := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    rw [Submodule.Quotient.mk_sub, hh, sub_self]
  exact hz

/-- The induced action of the original quotient by its two-core. -/
@[expose] def centralQuotientAction : Representation (ZMod 2) (L ⧸ pCore 2 L)
    D.chosenCentralQuotient :=
  QuotientGroup.lift (pCore 2 L) D.chosenCentralAction D.centralAction_core

/-- The quotient action retains the original projection. -/
theorem centralQuotientAction_mk (l : L) :
    D.centralQuotientAction (QuotientGroup.mk' (pCore 2 L) l) = D.chosenCentralAction l := rfl

/-- A simple quotient acts faithfully on the chosen central quotient. -/
theorem centralQuotientAction_injective (hs : IsSimpleGroup (L ⧸ pCore 2 L)) :
    Function.Injective D.centralQuotientAction := by
  let := hs
  apply D.centralQuotientAction.ker_eq_bot_iff.mp
  apply D.centralQuotientAction.normal_ker.eq_bot_or_eq_top.resolve_right
  intro ht
  apply D.centralAction_ne_one
  apply MonoidHom.ext
  intro l
  have hh := DFunLike.congr_fun (D.centralQuotientAction.ker_eq_top_iff.mp ht)
    (QuotientGroup.mk' (pCore 2 L) l)
  exact hh

/-- The original central-quotient kernel is exactly the component two-core. -/
theorem centralAction_ker_eq_core (hs : IsSimpleGroup (L ⧸ pCore 2 L)) :
    D.chosenCentralAction.ker = pCore 2 L := by
  apply le_antisymm _ D.centralAction_core
  intro l hl
  apply (QuotientGroup.eq_one_iff l).mp
  apply D.centralQuotientAction_injective hs
  change D.centralQuotientAction (QuotientGroup.mk' (pCore 2 L) l) = D.centralQuotientAction 1
  rw [D.centralQuotientAction_mk, map_one]
  exact hl

/-- Irreducibility descends along the same quotient projection. -/
theorem centralQuotientAction_irreducible : IsIrreducible D.centralQuotientAction := by
  apply (irreducible_comp_surjective_iff (QuotientGroup.mk' (pCore 2 L))
    (QuotientGroup.mk'_surjective _) D.centralQuotientAction).mp
  change IsIrreducible D.chosenCentralAction
  exact (irreducible_comp_surjective_iff _
    (subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm.surjective
    _).mpr D.irrPlus.isIrrPlus.choose_spec.2

include D in
/-- The same chosen subgroup detects the component two-core, without a module model. -/
theorem centralizer_eq_core_of_simple (hs : IsSimpleGroup (L ⧸ pCore 2 L)) :
    (centralizer (V : Set G)).subgroupOf L = pCore 2 L := by
  apply le_antisymm
  · intro l hl
    apply (D.centralAction_ker_eq_core hs).le
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v =>
      have hv : (v.val.toMul.val : G) ∈ V :=
        D.image_eq.le (mem_map_of_mem _ (mem_map_of_mem _ v.property))
      have hc : D.chosenAction l v = v := by
        apply Subtype.ext
        apply Additive.toMul.injective
        apply Subtype.ext
        apply Subtype.ext
        change (l : G) * (v.val.toMul.val : G) * (l : G)⁻¹ = (v.val.toMul.val : G)
        exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hl) _ hv).symm
      change Submodule.Quotient.mk (D.chosenAction l v) = Submodule.Quotient.mk v
      rw [hc]
  · intro l hl
    apply mem_centralizer_iff.mpr
    intro v hv
    obtain ⟨v', hv'⟩ := D.spaceEquiv.surjective ⟨v, hv⟩
    have hh := LinearMap.congr_fun (show D.chosenAction l = 1 from
      D.chosenAction_core hl) v'.toAdd
    have he := congrArg (fun w : D.space => (w.val.toMul.val : G)) hh
    have hv'' : (v'.toAdd.val.toMul.val : G) = v :=
      (D.spaceEquiv_apply v'.toAdd).symm.trans (congrArg Subtype.val hv')
    change (l : G) * (v'.toAdd.val.toMul.val : G) * (l : G)⁻¹ =
      (v'.toAdd.val.toMul.val : G) at he
    rw [hv''] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- Reindex the literal central action by the supplied alternating-five marking. -/
@[expose] def alternatingFiveCentralAction
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    Representation (ZMod 2) (alternatingGroup (Fin 5)) D.chosenCentralQuotient :=
  D.centralQuotientAction.comp e.symm.toMonoidHom

/-- The marking intertwines the literal component quotient map. -/
theorem alternatingFiveCentralAction_mk
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (l : L) :
    D.alternatingFiveCentralAction e (e (QuotientGroup.mk' (pCore 2 L) l)) =
      D.chosenCentralAction l := by
  change D.centralQuotientAction (e.symm (e (QuotientGroup.mk' (pCore 2 L) l))) = _
  rw [e.symm_apply_apply, D.centralQuotientAction_mk]

/-- The original A₅ central quotient is a faithful irreducible binary module. -/
theorem alternatingFiveCentralAction_faithful_irreducible
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    Function.Injective (D.alternatingFiveCentralAction e) ∧
      IsIrreducible (D.alternatingFiveCentralAction e) := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨(D.centralQuotientAction_injective e.isSimpleGroup).comp e.symm.injective, ?_⟩
  exact (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
    D.centralQuotientAction).mpr D.centralQuotientAction_irreducible

include D in
/-- The actual A₅ source choice detects O₂(L) before natural-module recognition. -/
theorem alternatingFive_chosen_centralizer
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    (centralizer (V : Set G)).subgroupOf L = pCore 2 L := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact D.centralizer_eq_core_of_simple e.isSimpleGroup

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
