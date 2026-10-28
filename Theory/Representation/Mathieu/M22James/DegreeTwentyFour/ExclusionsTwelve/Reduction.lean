module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.Preparation
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.Filtration

/-!
# The point constituent at binary degree twenty-four

The marked central scalar makes every binary invariant subspace of an F₄
representation stable under F₄. Thus scalar restriction preserves irreducibility.
For a faithful binary irreducible of degree twenty-four, the checked point
catalogue gives a simple submodule of degree six or eighteen. In the latter
case its annihilator in the dual has degree six. Classifying that small
submodule gives an actual nonzero natural or dual intertwiner into the point
restriction of the original representation or its dual.

The argument retains both branches and arbitrary nonsplit extensions. It
requires neither absolute irreducibility nor a prescribed endomorphism field.
These are reductions for Guralnick–Malle, Classification of 2F-modules I,
Proposition 5.1, pp.15–16, and Theorem 6.6/Table 6.7. They use the checked
SL₃(4) constituent catalogue; H.12.1 on pp.393–394 of Aschbacher–Smith supplies
the degree-twelve context but does not itself assert this larger degree gap.
-/

public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve
open Representation Uniqueness Uniqueness.PointRestriction
open Representation.SL3FourLocalCatalogue

section Scalars
variable {W : Type*} [AddCommGroup W] [Module Uniqueness.PointRestriction.F W]
  [Module (ZMod 2) W] [IsScalarTower (ZMod 2) Uniqueness.PointRestriction.F W]
  (τ : Representation Uniqueness.PointRestriction.F M22TripleCover W)
  (hs : ∀ w, τ scalar w = (QuadraticAlgebra.omega : Uniqueness.PointRestriction.F) • w)

private lemma scalar_expansion (r : Uniqueness.PointRestriction.F) (w : W) :
    r • w = r.re • w + r.im • ((QuadraticAlgebra.omega : Uniqueness.PointRestriction.F) • w) := by
  conv_lhs => rw [show r = algebraMap (ZMod 2) Uniqueness.PointRestriction.F r.re +
      r.im • (QuadraticAlgebra.omega : Uniqueness.PointRestriction.F) from
    QuadraticAlgebra.mk_eq_add_smul_omega r.re r.im]
  rw [add_smul, algebraMap_smul, smul_assoc]

/-- Binary and F₄ invariant subspaces agree when the central element acts by omega. -/
def restrictSubrepresentationEquiv :
    Subrepresentation (restrictScalars (k := ZMod 2) τ) ≃o Subrepresentation τ := by
  refine {
    toFun := fun U => {
      toSubmodule := {
        carrier := U
        zero_mem' := U.toSubmodule.zero_mem
        add_mem' := U.toSubmodule.add_mem
        smul_mem' := ?_ }
      apply_mem_toSubmodule := fun g _ hv => U.apply_mem_toSubmodule g hv }
    invFun := fun U => {
      toSubmodule := U.toSubmodule.restrictScalars (ZMod 2)
      apply_mem_toSubmodule := fun g _ hv => U.apply_mem_toSubmodule g hv }
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := fun {_ _} => Iff.rfl }
  · intro r w hw
    rw [scalar_expansion, ← hs]
    exact U.toSubmodule.add_mem (U.toSubmodule.smul_mem _ hw)
      (U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule scalar hw))
  · intro U
    apply Subrepresentation.toSubmodule_injective
    rfl
  · intro U
    apply Subrepresentation.toSubmodule_injective
    rfl

include hs in
/-- The marked central action makes restriction to the binary field irreducible. -/
theorem restrictScalars_isIrreducible [τ.IsIrreducible] :
    (restrictScalars (k := ZMod 2) τ).IsIrreducible :=
  (restrictSubrepresentationEquiv τ hs).isSimpleOrder_iff.mpr inferInstance

theorem restrictScalars_faithful (hf : Function.Injective τ) :
    Function.Injective (restrictScalars (k := ZMod 2) τ) := by
  intro g h he
  apply hf
  ext w
  exact LinearMap.congr_fun he w
end Scalars

section Binary
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) M22TripleCover V) [ρ.IsIrreducible]
  (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 24)

include hf hd in
/-- The entire point restriction cannot be simple at binary degree twenty-four. -/
theorem point_not_irreducible : ¬ (pointAction ρ).IsIrreducible := by
  intro hi
  let := hi
  have h := point_irreducible_finrank ρ hf hd.le
  omega

include hf hd in
/-- An actual simple submodule and its literal quotient have complementary degrees 6 and 18. -/
theorem point_filtration :
    ∃ N : Subrepresentation (pointAction ρ), N.toRepresentation.IsIrreducible ∧
      ((Module.finrank (ZMod 2) N.toSubmodule = 6 ∧
        Module.finrank (ZMod 2) (V ⧸ N.toSubmodule) = 18) ∨
       (Module.finrank (ZMod 2) N.toSubmodule = 18 ∧
        Module.finrank (ZMod 2) (V ⧸ N.toSubmodule) = 6 ∧
        N.quotientRepresentation.IsIrreducible)) := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨N, hi⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (pointAction ρ)
  let := hi
  have hn := point_simple_submodule_finrank ρ hf hd.le N
  have hsum := Submodule.finrank_quotient_add_finrank N.toSubmodule
  refine ⟨N, hi, ?_⟩
  rcases hn with hn | hn
  · exact Or.inl ⟨hn, by omega⟩
  · have hq : Module.finrank (ZMod 2) (V ⧸ N.toSubmodule) = 6 := by omega
    exact Or.inr ⟨hn, hq, isIrreducible_of_finrank_six N.quotientRepresentation
      (centralQuadratic_quotient _ (pointAction_centralQuadratic ρ hf) N) hq⟩

private def pointAnnihilator (N : Subrepresentation (pointAction ρ)) :
    Subrepresentation (pointAction ρ.dual) where
  toSubmodule := N.toSubmodule.dualAnnihilator
  apply_mem_toSubmodule g f hf := by
    rw [Submodule.mem_dualAnnihilator] at hf ⊢
    intro v hv
    have h := hf _ (N.apply_mem_toSubmodule g⁻¹ hv)
    simpa only [pointAction, MonoidHom.comp_apply, map_inv, dual_apply,
      Module.Dual.transpose_apply, LinearMap.comp_apply] using h

include hf hd in
/-- Annihilation supplies a small point submodule on one side of duality. -/
theorem point_six_submodule_or_dual :
    (∃ N : Subrepresentation (pointAction ρ),
      Module.finrank (ZMod 2) N.toSubmodule = 6) ∨
    (∃ N : Subrepresentation (pointAction ρ.dual),
      Module.finrank (ZMod 2) N.toSubmodule = 6) := by
  obtain ⟨N, _, h | h⟩ := point_filtration ρ hf hd
  · exact Or.inl ⟨N, h.1⟩
  · right
    refine ⟨pointAnnihilator ρ N, ?_⟩
    have he := Subspace.finrank_add_finrank_dualAnnihilator_eq N.toSubmodule
    change Module.finrank (ZMod 2) N.toSubmodule.dualAnnihilator = 6
    omega
end Binary
end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve
open Representation Uniqueness Uniqueness.PointRestriction
open Representation.SL3FourLocalCatalogue

section BinaryDual
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) M22TripleCover V) [ρ.IsIrreducible]

theorem dual_isIrreducible : IsIrreducible ρ.dual := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  refine ⟨fun W => ?_⟩
  let U : Subrepresentation ρ :=
    { toSubmodule := W.toSubmodule.dualCoannihilator
      apply_mem_toSubmodule g v hv := by
        rw [Submodule.mem_dualCoannihilator] at hv ⊢
        intro f hf
        have h := hv (ρ.dual g⁻¹ f) (W.apply_mem_toSubmodule g⁻¹ hf)
        simpa only [dual_apply, Module.Dual.transpose_apply,
          LinearMap.comp_apply, inv_inv] using h }
  have hd : U.toSubmodule.dualAnnihilator = W.toSubmodule :=
    Subspace.dualCoannihilator_dualAnnihilator_eq
  rcases eq_bot_or_eq_top U with h | h
  · right
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_bot
  · left
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_top

omit [ρ.IsIrreducible] in
theorem dual_faithful (hf : Function.Injective ρ) : Function.Injective ρ.dual := by
  intro g h he
  apply inv_injective
  apply hf
  ext v
  apply Module.eval_apply_injective (ZMod 2)
  ext f
  exact congrArg (fun T : Module.End (ZMod 2) (Module.Dual (ZMod 2) V) => T f v) he

omit [ρ.IsIrreducible] in
private theorem exists_point_map
    (hq : CentralQuadratic (pointAction ρ))
    (N : Subrepresentation (pointAction ρ)) (hn : Module.finrank (ZMod 2) N.toSubmodule = 6) :
    ∃ a : Constituent,
      ∃ f : IntertwiningMap (constituent a) (pointAction ρ), f ≠ 0 := by
  let := isIrreducible_of_finrank_six N.toRepresentation
    (centralQuadratic_subrepresentation _ hq N) hn
  obtain ⟨a, ⟨e⟩⟩ := exists_constituent_equiv N.toRepresentation
    (centralQuadratic_subrepresentation _ hq N) (by omega)
  let f : IntertwiningMap (constituent a) (pointAction ρ) := {
    toLinearMap := N.toSubmodule.subtype.comp e.symm.toLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro w
      exact congrArg Subtype.val (LinearMap.congr_fun (e.symm.isIntertwining' g) w) }
  refine ⟨a, f, ?_⟩
  have hi : Function.Injective f :=
    Subtype.val_injective.comp e.symm.toLinearEquiv.injective
  intro h
  obtain ⟨w, hw⟩ := exists_ne (0 : Representation.SL3FourLocalCatalogue.W)
  apply hw
  apply hi
  rw [h]
  rfl

/-- A concrete natural or dual constituent maps nontrivially into one of the two restrictions. -/
theorem point_constituent_or_dual (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 24) :
    (∃ a : Constituent, ∃ f : IntertwiningMap (constituent a) (pointAction ρ), f ≠ 0) ∨
    (∃ a : Constituent, ∃ f : IntertwiningMap (constituent a) (pointAction ρ.dual), f ≠ 0) := by
  rcases point_six_submodule_or_dual ρ hf hd with ⟨N, hN⟩ | ⟨N, hN⟩
  · exact Or.inl (exists_point_map ρ (pointAction_centralQuadratic ρ hf) N hN)
  · let := dual_isIrreducible ρ
    exact Or.inr (exists_point_map ρ.dual
      (pointAction_centralQuadratic ρ.dual (dual_faithful ρ hf)) N hN)
end BinaryDual
end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve
