module
public import Theory.Representation.SL2BinaryHyperplanes
public import Theory.Representation.SpecialLinearThreeTransitivity
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry
public import Theory.Representation.G2NaturalTransitivity
public import Theory.Representation.G2OrthogonalCover.Universal

/-!
# Binary hyperplanes of the marked natural quotients

Every binary functional factors through a fixed nonzero binary functional
on the coefficient field. Transitivity on nonzero field functionals then
gives binary-hyperplane transitivity for the full SL₃, Sp₄ and G₂ actions.
The symplectic and G₂ calculations use their actual nondegenerate invariant
pairings; the linear calculation uses determinant-one matrix transposition.
The ambient application in `Source` retains the original central kernel.

Source: Aschbacher--Smith, proof of 11.2.2, printed p.767. The orbit argument
works in every degree, and the model actions are the existing attributed
CFSG/ATLAS constructions; no additional ATLAS source is copied here.
-/

public noncomputable section
open Subgroup Representation Matrix
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
section BinaryDual
variable {F X : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  [AddCommGroup X] [Module F X] [Module (ZMod 2) X] [IsScalarTower (ZMod 2) F X]
  [FiniteDimensional F X]

private def dualCompose (ell : F →ₗ[ZMod 2] ZMod 2) :
    Module.Dual F X →ₗ[ZMod 2] Module.Dual (ZMod 2) X where
  toFun f := ell.comp (f.restrictScalars (ZMod 2))
  map_add' f g := by ext x; simp
  map_smul' a f := by ext x; simp

omit [Finite F] [FiniteDimensional F X] in
private theorem dualCompose_injective (ell : F →ₗ[ZMod 2] ZMod 2) (hell : ell 1 = 1) :
    Function.Injective (dualCompose (X := X) ell) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_bot_iff.mp
  intro f hf
  change f = 0
  by_contra hn
  obtain ⟨x,hx⟩ := (LinearMap.surjective_iff_ne_zero.mpr hn) 1
  have he := LinearMap.congr_fun hf x
  change ell (f x) = 0 at he
  rw [hx,hell] at he
  exact one_ne_zero he

/-- Every binary functional on a field space is a fixed nonzero binary
functional of the field composed with a field-linear functional. -/
theorem binary_functional_factor (ell : F →ₗ[ZMod 2] ZMod 2) (hell : ell 1 = 1)
    (f : Module.Dual (ZMod 2) X) :
    ∃ g : Module.Dual F X, ell.comp (g.restrictScalars (ZMod 2)) = f := by
  let : Finite X := Module.finite_of_finite F
  have hd : Module.finrank (ZMod 2) (Module.Dual F X) =
      Module.finrank (ZMod 2) (Module.Dual (ZMod 2) X) := by
    rw [Subspace.dual_finrank_eq]
    rw [← Module.finrank_mul_finrank (ZMod 2) F (Module.Dual F X),
      ← Module.finrank_mul_finrank (ZMod 2) F X, Subspace.dual_finrank_eq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp
    (dualCompose_injective ell hell) f

/-- A binary hyperplane contains a field hyperplane, with no splitting
assumption on any ambient central cover. -/
theorem field_hyperplane_in_binary (U : Submodule (ZMod 2) X)
    (hU : Module.finrank (ZMod 2) U + 1 = Module.finrank (ZMod 2) X) :
    ∃ Q : Submodule F X, Module.finrank F Q + 1 = Module.finrank F X ∧
      Q.restrictScalars (ZMod 2) ≤ U := by
  let : Finite X := Module.finite_of_finite F
  have htop : U < ⊤ := by
    apply lt_of_le_of_ne le_top
    intro he
    rw [he,finrank_top] at hU
    omega
  obtain ⟨f,hf,hUf⟩ := U.exists_le_ker_of_lt_top htop
  have hker : U = f.ker := Submodule.eq_of_le_of_finrank_eq hUf (by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    omega)
  obtain ⟨ell,hell⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) (one_ne_zero : (1:F) ≠ 0)
  obtain ⟨g,hg⟩ := binary_functional_factor ell hell f
  have hg0 : g ≠ 0 := by intro h; simp [h] at hg; exact hf hg.symm
  refine ⟨g.ker,Module.Dual.finrank_ker_add_one_of_ne_zero hg0,?_⟩
  intro x hx
  rw [hker]
  change f x = 0
  rw [←hg]
  change ell (g x) = 0
  rw [show g x=0 from hx,map_zero]

/-- Transitivity on nonzero field functionals gives transitivity on binary
hyperplanes under the same literal representation. -/
theorem binary_hyperplanes_transitive_of_dual {H : Type*} [Group H]
    (ρ : Representation F H X)
    (ht : ∀ f g : Module.Dual F X, f ≠ 0 → g ≠ 0 →
      ∃ a : H, f.comp (ρ a) = g)
    (U W : Submodule (ZMod 2) X)
    (hU : Module.finrank (ZMod 2) U + 1 = Module.finrank (ZMod 2) X)
    (hW : Module.finrank (ZMod 2) W + 1 = Module.finrank (ZMod 2) X) :
    ∃ a : H, U.map ((ρ a).restrictScalars (ZMod 2)) = W := by
  let : Finite X := Module.finite_of_finite F
  have ker_rep (Y : Submodule (ZMod 2) X)
      (hY : Module.finrank (ZMod 2) Y + 1 = Module.finrank (ZMod 2) X) :
      ∃ f : Module.Dual (ZMod 2) X, f ≠ 0 ∧ Y = f.ker := by
    have htop : Y < ⊤ := by
      apply lt_of_le_of_ne le_top
      intro he
      rw [he,finrank_top] at hY
      omega
    obtain ⟨f,hf,hYf⟩ := Y.exists_le_ker_of_lt_top htop
    exact ⟨f,hf,Submodule.eq_of_le_of_finrank_eq hYf (by
      have := Module.Dual.finrank_ker_add_one_of_ne_zero hf
      omega)⟩
  obtain ⟨f,hf,rfl⟩ := ker_rep U hU
  obtain ⟨g,hg,rfl⟩ := ker_rep W hW
  obtain ⟨ell,hell⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) (one_ne_zero : (1:F) ≠ 0)
  obtain ⟨f',hf'⟩ := binary_functional_factor ell hell f
  obtain ⟨g',hg'⟩ := binary_functional_factor ell hell g
  have hf0 : f' ≠ 0 := by intro h; simp [h] at hf'; exact hf hf'.symm
  have hg0 : g' ≠ 0 := by intro h; simp [h] at hg'; exact hg hg'.symm
  obtain ⟨a,ha⟩ := ht g' f' hg0 hf0
  have hab (x : X) : g (ρ a x) = f x := by
    rw [←hf',←hg']
    exact congrArg ell (LinearMap.congr_fun ha x)
  refine ⟨a,?_⟩
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (hab y).trans hy
  · intro hx
    refine ⟨ρ a⁻¹ x,?_,?_⟩
    · change f (ρ a⁻¹ x) = 0
      rw [←hab,ρ.self_inv_apply]
      exact hx
    · exact ρ.self_inv_apply a x
end BinaryDual
section Models
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem sl3_dual_transitive (f g : Module.Dual F (Fin 3 → F))
    (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ a : Matrix.SpecialLinearGroup (Fin 3) F,
      f.comp (Representation.specialLinearNatural 3 a) = g := by
  let coeff (h : Module.Dual F (Fin 3 → F)) : Fin 3 → F :=
    fun i => h (Pi.single i 1)
  have happ (h : Module.Dual F (Fin 3 → F)) (x : Fin 3 → F) :
      h x = dotProduct (coeff h) x := by
    conv_lhs => rw [show x = ∑ i, x i • Pi.single i 1 by ext i; fin_cases i <;> simp [Fin.sum_univ_three]]
    simp [coeff,dotProduct,mul_comm]
  have hne (h : Module.Dual F (Fin 3 → F)) (hh : h ≠ 0) : coeff h ≠ 0 := by
    intro he
    apply hh
    apply LinearMap.ext
    intro x
    rw [happ,he,zero_dotProduct]
    rfl
  obtain ⟨a,ha⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three
    (coeff f) (coeff g) (hne f hf) (hne g hg)
  refine ⟨a.transpose,?_⟩
  apply LinearMap.ext
  intro x
  change f (a.val.transpose *ᵥ x) = g x
  rw [happ,happ,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose,ha]

/-- The full SL₃ action is transitive on binary hyperplanes, in every degree. -/
theorem sl3_binary_hyperplanes (U W : Submodule (ZMod 2) (Fin 3 → F))
    (hU : Module.finrank (ZMod 2) U + 1 = Module.finrank (ZMod 2) (Fin 3 → F))
    (hW : Module.finrank (ZMod 2) W + 1 = Module.finrank (ZMod 2) (Fin 3 → F)) :
    ∃ a : Matrix.SpecialLinearGroup (Fin 3) F,
      U.map ((Representation.specialLinearNatural 3 a).restrictScalars (ZMod 2)) = W :=
  binary_hyperplanes_transitive_of_dual _ sl3_dual_transitive U W hU hW

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem dual_transitive_of_pairing {H X : Type*} [Group H]
    [AddCommGroup X] [Module F X] [FiniteDimensional F X]
    (ρ : Representation F H X) (B : X →ₗ[F] Module.Dual F X)
    (hB : Function.Injective B)
    (hpres : ∀ a x y, B (ρ a x) (ρ a y) = B x y)
    (ht : ∀ x y : X, x ≠ 0 → y ≠ 0 → ∃ a : H, ρ a x = y)
    (f g : Module.Dual F X) (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ a : H, f.comp (ρ a) = g := by
  have honto : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).mp hB
  obtain ⟨v,rfl⟩ := honto f
  obtain ⟨w,rfl⟩ := honto g
  have hv : v ≠ 0 := by intro h; exact hf (by rw [h,map_zero])
  have hw : w ≠ 0 := by intro h; exact hg (by rw [h,map_zero])
  obtain ⟨a,ha⟩ := ht w v hw hv
  refine ⟨a,?_⟩
  ext x
  change B v (ρ a x) = B w x
  rw [←ha,hpres]

open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.TwoLocalCover

/-- Natural Sp₄ acts transitively on binary hyperplanes, without choosing a
complement in any central cover. -/
theorem sp4_binary_hyperplanes (U W : Submodule (ZMod 2) (Vector F))
    (hU : Module.finrank (ZMod 2) U + 1 = Module.finrank (ZMod 2) (Vector F))
    (hW : Module.finrank (ZMod 2) W + 1 = Module.finrank (ZMod 2) (Vector F)) :
    ∃ a : Sp F, U.map ((symplecticNatural 2 a).restrictScalars (ZMod 2)) = W := by
  refine binary_hyperplanes_transitive_of_dual (symplecticNatural (k := F) 2) ?_ U W hU hW
  have hi : Function.Injective (form F) := by
    apply LinearMap.ker_eq_bot.mp
    apply le_bot_iff.mp
    intro x hx
    exact (form_nondegenerate (F := F)).1 x (fun y => LinearMap.congr_fun hx y)
  have hp (a : Sp F) (x y : Vector F) :
      form F (symplecticNatural 2 a x) (symplecticNatural 2 a y) = form F x y :=
    preserves_form a x y
  have ht (x y : Vector F) (hx : x ≠ 0) (hy : y ≠ 0) :
      ∃ a : Sp F, symplecticNatural 2 a x = y := nonzero_vector_transitive hx hy
  exact dual_transitive_of_pairing (symplecticNatural (k := F) 2) (form F) hi hp ht

/-- The actual six-dimensional G₂ quotient has one binary hyperplane orbit. -/
theorem g2_binary_hyperplanes [CharP F 2]
    (U W : Submodule (ZMod 2) (Atlas.G2.Natural.Space F))
    (hU : Module.finrank (ZMod 2) U + 1 =
      Module.finrank (ZMod 2) (Atlas.G2.Natural.Space F))
    (hW : Module.finrank (ZMod 2) W + 1 =
      Module.finrank (ZMod 2) (Atlas.G2.Natural.Space F)) :
    ∃ a : Atlas.G2.Model F,
      U.map ((g2Natural F a).restrictScalars (ZMod 2)) = W := by
  refine binary_hyperplanes_transitive_of_dual (g2Natural F) ?_ U W hU hW
  apply dual_transitive_of_pairing (g2Natural F)
    (Atlas.G2.Natural.OrthogonalCover.naturalPairing F)
    (Atlas.G2.Natural.OrthogonalCover.naturalPairing_injective F)
  · intro a x y
    obtain ⟨x,rfl⟩ := Atlas.G2.Natural.mk_surjective F x
    obtain ⟨y,rfl⟩ := Atlas.G2.Natural.mk_surjective F y
    simp only [g2Natural, Atlas.G2.Natural.action_mk,
      Atlas.G2.Natural.OrthogonalCover.naturalPairing_mk,
      Atlas.G2.Natural.traceZeroAction_val, Atlas.SplitOctonion.automorphism_normPolar]
  · intro x y hx hy
    exact Atlas.G2.Natural.action_transitive hx hy
end Models

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
