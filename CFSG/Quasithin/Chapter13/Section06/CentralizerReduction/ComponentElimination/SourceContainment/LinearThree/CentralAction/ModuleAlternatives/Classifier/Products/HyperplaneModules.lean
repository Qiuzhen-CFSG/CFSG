module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products.Selection
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Transport
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary

/-!
# Component modules in the hyperplane product branch

The actual component is one of the two original factors by the proved product
placement theorem. For the first factor, simplicity and perfectness make its
action on its three-dimensional moved space faithful. A binary basis then
identifies that action with GL₃(2) = SL₃(2), including an actor isomorphism and
an intertwiner. Its fixed space is zero, so these coordinates descend through
the literal component-fixed quotient. Perfectness gives commutator generation.

For the second factor, the source already identifies the moved space itself
with at most two copies of the same natural module. Zero copies contradict
faithfulness; evaluation gives the one-copy coordinates, and two copies retain
the supplied single actor identification. The SL₂ row is excluded by the proved
actor comparison. No splitting of the ambient module or further classification
input is needed. The original hyperplane record, maps and subspaces are retained.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.6(5),
printed p.105, and its component-module application in 13.6.20, printed p.931.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {C : Subgroup D}

private theorem moved_ne_bot (hf : Function.Injective ρ)
    (e : C ≃* Matrix.PSL3Two.PSL) : moved ρ C ≠ ⊥ := by
  intro hz
  have hfix := (subspaceCommutator_eq_bot_iff ρ ⊤ C).mp hz
  have htriv (g : C) : g = 1 := by
    apply Subtype.ext
    apply hf
    ext v
    simpa using hfix (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) V)) g
  let : Subsingleton C := ⟨fun g h => (htriv g).trans (htriv h).symm⟩
  let : Nontrivial C := e.symm.injective.nontrivial
  exact false_of_nontrivial_of_subsingleton C

private theorem moved_faithful [C.Normal]
    (hf : Function.Injective ρ) (e : C ≃* Matrix.PSL3Two.PSL) :
    Function.Injective ((MovedSection.ofNormal ρ C).space.toRepresentation.comp C.subtype) := by
  let s := MovedSection.ofNormal ρ C
  let σ := s.space.toRepresentation.comp C.subtype
  let : IsSimpleGroup Matrix.PSL3Two.SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup C := (e.trans Matrix.PSL3Two.equiv.symm).isSimpleGroup
  let : IsQuasisimple C := component_quasisimple e
  rcases (inferInstance : σ.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact σ.ker_eq_bot_iff.mp hb
  have hs : σ = 1 := MonoidHom.ker_eq_top_iff.mp ht
  have hm : moved ρ C ≤ fixedSpace ρ C := by
    intro v hv g
    have h := LinearMap.congr_fun (congrArg (fun t => t g) hs) (⟨v, hv⟩ : s.space.toSubmodule)
    exact congrArg Subtype.val h
  have hfix : (⊤ : Submodule (ZMod 2) V) ≤ fixedSpace ρ C :=
    le_fixedSpace_of_commutator_le_fixedSpace ρ C ⊤
      (le_subspaceStabilizer ρ ⊤ (by simp)) hm
  exact (moved_ne_bot hf e ((subspaceCommutator_eq_bot_iff ρ ⊤ C).mpr hfix)).elim

private theorem natural_coordinates {A W : Type*} [Group A]
    [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (σ : Representation (ZMod 2) A W) (eA : A ≃* Matrix.PSL3Two.PSL)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) W = 3) :
    Nonempty (ActionEquiv σ BinaryLinearThree.W) := by
  classical
  let b := Module.finBasisOfFinrankEq (ZMod 2) W hd
  let e := b.equivFun
  let l : A →* ((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) := {
    toFun := fun g => (e.symm.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W (σ.asGroupHom g))).trans e
    map_one' := by ext v; simp
    map_mul' := by intro g h; ext v; simp }
  let toGL := (LinearMap.GeneralLinearGroup.generalLinearEquiv
      (ZMod 2) (Fin 3 → ZMod 2)).symm.trans Matrix.GeneralLinearGroup.toLin.symm
  let f : A →* Matrix.PSL3Two.SL :=
    Matrix.PSL3Two.equivGL.symm.toMonoidHom.comp (toGL.toMonoidHom.comp l)
  have heq (g : A) (v : Fin 3 → ZMod 2) : (f g).val.mulVec v = l g v := by
    have hmat : Matrix.SpecialLinearGroup.toGL (f g) = toGL (l g) := by
      dsimp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [← Matrix.PSL3Two.equivGL_apply, MulEquiv.apply_symm_apply]
    have hh := congrArg (fun t : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) =>
      (Matrix.GeneralLinearGroup.toLin t : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) v) hmat
    simp only [toGL, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at hh
    change (f g).val.mulVec v =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → ZMod 2)
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → ZMod 2)).symm
          (l g))) v at hh
    simpa only [MulEquiv.apply_symm_apply] using hh
  have hfi : Function.Injective f := by
    intro g h hgh
    apply hf
    ext v
    apply e.injective
    have hh := congrArg (fun t : Matrix.PSL3Two.SL => t.val.mulVec (e v)) hgh
    simpa [heq, l, Representation.asGroupHom_apply] using hh
  have hcard : Nat.card Matrix.PSL3Two.SL ≤ Nat.card A := by
    rw [Nat.card_congr eA.toEquiv, ← Nat.card_congr Matrix.PSL3Two.equiv.toEquiv]
  refine ⟨⟨MulEquiv.ofBijective f (hfi.bijective_of_nat_card_le hcard), e, ?_⟩⟩
  intro g v
  change e (σ g v) = (f g).val.mulVec (e v)
  rw [heq]
  simp [l, Representation.asGroupHom_apply]

-- The quotient proof is the perfect-actor argument used in Chapter B's
-- ComponentReduction/NaturalClosure/SecondComponent, specialized to [V,C].
private theorem moved_generated [C.Normal] [Group.IsPerfect C] :
    subspaceCommutator ρ (moved ρ C) C = moved ρ C := by
  let J := (MovedSection.ofNormal ρ C).space
  let M := subspaceCommutator ρ J.toSubmodule C
  have hJstab : C ≤ subspaceStabilizer ρ J.toSubmodule := by
    apply le_subspaceStabilizer
    intro k hk v hv
    exact J.apply_mem_toSubmodule k hv
  have hMstab : C ≤ subspaceStabilizer ρ M :=
    subspaceCommutator_invariant_normalizer ρ hJstab C.le_normalizer
  have hMle : M ≤ J.toSubmodule := subspaceCommutator_le_of_invariant ρ hJstab
  let Mrep : Subrepresentation (ρ.comp C.subtype) :=
    ⟨M, by intro k v hv; exact (hMstab k.property v).2 hv⟩
  let qρ := Mrep.quotientRepresentation
  have hqC : subspaceCommutator qρ ⊤ (⊤ : Subgroup C) ≤ fixedSpace qρ ⊤ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, _, v, _, rfl⟩
    intro k
    induction v using Submodule.Quotient.induction_on with
    | _ w =>
      change qρ k (qρ x (Mrep.toSubmodule.mkQ w) - Mrep.toSubmodule.mkQ w) =
        qρ x (Mrep.toSubmodule.mkQ w) - Mrep.toSubmodule.mkQ w
      rw [map_sub, Subrepresentation.quotientRepresentation_mk,
        Subrepresentation.quotientRepresentation_mk]
      apply (Submodule.Quotient.eq M).mpr
      have hdJ : ρ x.val w - w ∈ J.toSubmodule :=
        Submodule.subset_span ⟨x.val, x.property, w, Submodule.mem_top, rfl⟩
      exact Submodule.subset_span
        ⟨k.val, k.val.property, ρ x.val w - w, hdJ, by
          simp only [map_sub, ← Module.End.mul_apply]
          rfl⟩
  have hqfix : (⊤ : Submodule (ZMod 2) (V ⧸ M)) ≤ fixedSpace qρ (⊤ : Subgroup C) :=
    le_fixedSpace_of_commutator_le_fixedSpace qρ (⊤ : Subgroup C) ⊤
      (le_subspaceStabilizer qρ ⊤ (by simp)) hqC
  have hJleM : J.toSubmodule ≤ M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, v, _, rfl⟩
    have hfix := hqfix (show Mrep.toSubmodule.mkQ v ∈
      (⊤ : Submodule (ZMod 2) (V ⧸ M)) from by trivial)
    have hfixx := hfix ⟨⟨x, hx⟩, by simp⟩
    change Mrep.toSubmodule.mkQ (ρ x v) = Mrep.toSubmodule.mkQ v at hfixx
    apply (Submodule.Quotient.mk_eq_zero M).mp
    change Mrep.toSubmodule.mkQ (ρ x v - v) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hfixx
  exact le_antisymm hMle hJleM

private theorem natural_case [C.Normal]
    (eC : C ≃* Matrix.PSL3Two.PSL) (s : MovedSection ρ C)
    (e : ActionEquiv (s.space.toRepresentation.comp C.subtype) BinaryLinearThree.W) :
    LinearThreeModuleCase ρ C := by
  let : IsQuasisimple C := component_quasisimple eC
  have hc : s.central.toSubmodule = ⊥ := by
    rw [s.central_eq]
    apply bot_unique
    intro v hv
    have hfix : e.linearEquiv v ∈
        Representation.OneCohomology.fixed BinaryLinearThree.W := by
      intro g
      obtain ⟨a, rfl⟩ := e.groupEquiv.surjective g
      exact (e.intertwines a v).symm.trans (congrArg e.linearEquiv (hv a))
    rw [Representation.OneCohomology.SLHigherNatural.fixed_eq_bot (by decide : 2 ≤ 3)] at hfix
    apply e.linearEquiv.injective
    simpa using hfix
  let q := s.central.toSubmodule.quotEquivOfEqBot hc
  refine .natural s ?_ ⟨e.groupEquiv, q.trans e.linearEquiv, ?_⟩
  · rw [s.space_eq]
    exact moved_generated
  · intro g v
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      change e.linearEquiv (q (Submodule.Quotient.mk (s.space.toRepresentation g v))) =
        BinaryLinearThree.W (e.groupEquiv g) (e.linearEquiv (q (Submodule.Quotient.mk v)))
      simpa only [q, Submodule.quotEquivOfEqBot_apply_mk, MonoidHom.comp_apply,
        Subgroup.subtype_apply] using e.intertwines g v

private noncomputable def sectionOfSpace [C.Normal] (U : Subrepresentation ρ)
    (hU : U.toSubmodule = moved ρ C) : MovedSection ρ C :=
  ⟨U, hU, ⟨fixedSpace U.toRepresentation C, fun g v hv =>
    (fixedSpace_stable_of_normal U.toRepresentation C (mem_top g) v).2 hv⟩, rfl⟩

/-- Dimension three on the actual faithful component's moved space supplies
natural coordinates on its literal component-fixed quotient. -/
theorem hyperplane_first_module [C.Normal] [Module.Finite (ZMod 2) V]
    (hf : Function.Injective ρ) (e : C ≃* Matrix.PSL3Two.PSL)
    (hd : Module.finrank (ZMod 2) (moved ρ C) = 3) : LinearThreeModuleCase ρ C := by
  let s := MovedSection.ofNormal ρ C
  obtain ⟨a⟩ := natural_coordinates (s.space.toRepresentation.comp C.subtype) e
    (moved_faithful hf e) hd
  exact natural_case e s a

/-- Exhaust both source rows and all three allowed multiplicities on the
original second moved space. -/
theorem hyperplane_second_module [C.Normal]
    (hf : Function.Injective ρ) (e : C ≃* Matrix.PSL3Two.PSL)
    {U : Subrepresentation ρ} (hm : U.toSubmodule = moved ρ C)
    (h : HyperplaneSecondCase ρ C U) : LinearThreeModuleCase ρ C := by
  let s := sectionOfSpace U hm
  cases h with
  | linearTwo F hn =>
    obtain ⟨a⟩ := hn
    exact (no_linearTwo_factor e le_rfl F a.groupEquiv).elim
  | linearThree r hr hn =>
    obtain ⟨a⟩ := hn
    interval_cases r
    · have hzero : U.toSubmodule = ⊥ := by
        apply bot_unique
        intro v hv
        have hh : a.linearEquiv (⟨v, hv⟩ : U) = a.linearEquiv 0 := Subsingleton.elim _ _
        exact congrArg Subtype.val (a.linearEquiv.injective hh)
      exact (moved_ne_bot hf e (hm.symm.trans hzero)).elim
    · let one : (Fin 1 → BinaryLinearThree.Vector) ≃ₗ[ZMod 2] BinaryLinearThree.Vector :=
        LinearEquiv.funUnique (Fin 1) (ZMod 2) BinaryLinearThree.Vector
      apply natural_case e s
      refine ⟨a.groupEquiv, a.linearEquiv.trans one, ?_⟩
      intro g v
      exact congrFun (a.intertwines g v) 0
    · exact .doubled s a

/-- B.5.6(5) gives exactly the component module alternatives used in 13.6.20.
No classification input or splitting hypothesis remains. -/
theorem hyperplane_moduleCase [Finite D] {𝒦 : GroupClass}
    (hyp : FFHypothesis 𝒦 ρ) [C.Normal] (e : C ≃* Matrix.PSL3Two.PSL)
    (c : HyperplaneCase ρ) : LinearThreeModuleCase ρ C := by
  let : Module.Finite (ZMod 2) V := hyp.finite_module
  rcases hyperplane_component_eq e c with h | h
  · subst C
    exact hyperplane_first_module hyp.faithful e c.firstDimension
  · subst C
    exact hyperplane_second_module hyp.faithful e c.secondSpace_eq c.secondCase

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products
