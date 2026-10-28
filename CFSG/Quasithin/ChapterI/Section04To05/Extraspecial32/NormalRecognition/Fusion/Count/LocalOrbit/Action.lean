module
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.Fusion.Count.Preparation
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Kernel
public import Theory.GroupTheory.PGroup.ExtraspecialInvolutionCosetAction
public import Theory.GroupTheory.Fitting.Centralizer
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The literal local action on singular central cosets

The centralizer is solvable, since its extraspecial core has symmetric-three
quotient. Fitting self-centralization and the inner kernel of the quaternion
central-quotient action show that the kernel of the H-action on Q/Z(Q) is
exactly Q. Relative quaternion normality fixes both actual factors.

`GridModel` specifies equivariant coordinates on the singular nonzero cosets,
including a nontrivial cubic in both degree-three factor actions. Its construction
and the finite grid orbit calculation remain separate proof obligations.
`CosetProfile` records the exact quotient orbits required by the lifting step.
Neither structure is asserted to follow merely by its definition.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 2.2–2.3, particularly 2.3(2)(b).
-/

namespace CFSG.Quasithin.Extraspecial32
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace FusionCount.LocalOrbit
@[expose] public def quotientAction (z : G) :
    Centralizer z →* MulAut (Core z ⧸ center (Core z)) :=
  (quotientAut (center (Core z))).comp MulAut.conjNormal
@[expose] public def cosetAction (z : G) :
    Centralizer z →* Equiv.Perm (CentralInvolutionCosets (Core z)) :=
  centralInvolutionCosetAction.comp MulAut.conjNormal
@[expose] public def cosetOrbit (z : G) (v : CentralInvolutionCosets (Core z)) :
    Set (CentralInvolutionCosets (Core z)) := Set.range (fun a => cosetAction z a v)
/-- Coordinates for the actual nine singular cosets and their two factor actions. -/
public structure GridModel (z : G) where
  left : (Centralizer z ⧸ Core z) →* Equiv.Perm (Fin 3)
  right : (Centralizer z ⧸ Core z) →* Equiv.Perm (Fin 3)
  left_three : ∃ a, orderOf (left a) = 3
  right_three : ∃ a, orderOf (right a) = 3
  coordinates : CentralInvolutionCosets (Core z) ≃ (Fin 3 × Fin 3)
  equivariant : ∀ (a : Centralizer z) (v : CentralInvolutionCosets (Core z)),
    coordinates (cosetAction z a v) =
      (left (QuotientGroup.mk' (Core z) a) (coordinates v).1,
       right (QuotientGroup.mk' (Core z) a) (coordinates v).2)
/-- The exact orbit information needed for lifting to the eighteen involutions. -/
@[expose] public def CosetProfile (z : G) : Prop :=
  ∃ S : Set (CentralInvolutionCosets (Core z)), S.ncard = 3 ∧
    (∀ v ∈ S, cosetOrbit z v = S) ∧
    (∀ v ∉ S, (cosetOrbit z v).ncard = 6)
end FusionCount.LocalOrbit

namespace Hypotheses
public theorem localOrbit_centralizer_solvable (h : Hypotheses z) :
    Group.IsSolvable (Centralizer z) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
  let : Group.IsSolvable (Centralizer z ⧸ Core z) :=
    Group.isSolvable_of_isSolvable_injective (f := h.quotient_model.some.toMonoidHom)
      h.quotient_model.some.injective
  let : Group.IsNilpotent (Core z) :=
    (IsPGroup.of_card (p := 2) (n := 5) h.core_card).isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (Core z)).mpr
    ⟨inferInstance, inferInstance⟩

public theorem localOrbit_core_selfCentralizing (h : Hypotheses z) :
    centralizer (Core z : Set (Centralizer z)) ≤ Core z :=
  (centralizer_le (show fittingSubgroup (Centralizer z) ≤ Core z from
    fitting_le_generalizedFitting _)).trans
    ((centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable
      h.localOrbit_centralizer_solvable).trans (fitting_le_generalizedFitting _))

public theorem localOrbit_quotientAction_ker (h : Hypotheses z) :
    (FusionCount.LocalOrbit.quotientAction z).ker = Core z := by
  obtain ⟨d⟩ := h.quaternionCentralProduct
  ext a
  change quotientAut (center (Core z)) (MulAut.conjNormal a) = 1 ↔ a ∈ Core z
  rw [d.quotientAut_eq_one_iff_inner]
  constructor
  · rintro ⟨q, hq⟩
    have hcentral : (q : Centralizer z)⁻¹ * a ∈ centralizer (Core z : Set (Centralizer z)) := by
      intro x hx
      have he := congrArg Subtype.val (DFunLike.congr_fun hq (⟨x, hx⟩ : Core z))
      change (q : Centralizer z) * x * (q : Centralizer z)⁻¹ = a * x * a⁻¹ at he
      apply (commute_iff_eq _ _).mp
      apply Commute.symm
      apply (commute_iff_eq _ _).mpr
      apply mul_inv_eq_iff_eq_mul.mp
      calc
        ((q : Centralizer z)⁻¹ * a) * x * ((q : Centralizer z)⁻¹ * a)⁻¹ =
            (q : Centralizer z)⁻¹ * (a * x * a⁻¹) * q := by group
        _ = x := by rw [← he]; group
    have hh := (Core z).mul_mem q.property (h.localOrbit_core_selfCentralizing hcentral)
    simpa only [mul_inv_cancel_left] using hh
  · intro ha
    exact ⟨⟨a, ha⟩, by ext x; rfl⟩

/-- The central-quotient action descended through the literal source quotient. -/
@[expose] public def localOrbit_outerAction (h : Hypotheses z) :
    (Centralizer z ⧸ Core z) →* MulAut (Core z ⧸ center (Core z)) :=
  QuotientGroup.lift (Core z) (FusionCount.LocalOrbit.quotientAction z)
    h.localOrbit_quotientAction_ker.ge

/-- This is the faithful H/Q action used in the local orthogonal calculation. -/
public theorem localOrbit_outerAction_injective (h : Hypotheses z) :
    Function.Injective h.localOrbit_outerAction :=
  (QuotientGroup.injective_lift_iff (Core z) (FusionCount.LocalOrbit.quotientAction z)
    h.localOrbit_quotientAction_ker.ge).mpr h.localOrbit_quotientAction_ker.symm

@[simp] public theorem localOrbit_outerAction_mk (h : Hypotheses z) (a : Centralizer z) :
    h.localOrbit_outerAction (QuotientGroup.mk' (Core z) a) =
      FusionCount.LocalOrbit.quotientAction z a := rfl

public theorem localOrbit_factor_preserved (_h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : QuaternionCentralProductData (Core z))
    (a : Centralizer z) :
    d.left.map (MulAut.conjNormal a).toMonoidHom = d.left ∧
    d.right.map (MulAut.conjNormal a).toMonoidHom = d.right := by
  have hfactor (R : Subgroup (Core z)) (hR : Nonempty (R ≃* QuaternionGroup 2)) :
      R.map (MulAut.conjNormal a).toMonoidHom = R := by
    let : (R.map (Core z).subtype).Normal := hn R hR
    apply map_injective (Core z).subtype_injective
    rw [map_map]
    change R.map ((MulAut.conj a).toMonoidHom.comp (Core z).subtype) = _
    rw [← map_map]
    exact mem_normalizer_iff_map_conj_eq.mp
      (by rw [normalizer_eq_top]; trivial)
  exact ⟨hfactor d.left d.left_model, hfactor d.right d.right_model⟩
end Hypotheses
end CFSG.Quasithin.Extraspecial32
