module

public import Theory.SpecificGroups.OrthogonalFourBinary.SingularOrbit
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.QuadraticForm.Basis
public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Coordinates for a binary plus-type quadratic four-space

A nondegenerate four-dimensional quadratic space over `ZMod 2` with a
two-dimensional totally singular subspace is isometric to `OrthogonalFourBinary.form`,
the orthogonal sum of two anisotropic binary planes.

Choose a complement to the singular plane. Polar duality identifies the singular
plane with the complement's dual. A bilinear representative of the restricted
quadratic form gives a linear shear that makes the complement singular, yielding
the evaluation form `q(f, u) = f(u)`. A basis gives `ac + bd`, and an explicit
invertible coordinate change identifies this with the literal form in
`SingularOrbit`.

The complement and shear argument is adapted from the private
`HyperbolicModel.exists_dual_isometry` in
`Theory/SpecificGroups/Monster/Construction/LocalC/SourceNormalizer/Orientation/QuarterTurnGeneration/HyperbolicModel.lean`;
no Monster results are used or imported here.

Source motivation: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), printed pp.1121–1122 and 1140–1141.
-/

public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace OrthogonalFourBinary
open Module
section General
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

private def shear {W U : Type*} [AddCommGroup W] [Module K W]
    [AddCommGroup U] [Module K U] (t : U →ₗ[K] W) : (W × U) ≃ₗ[K] (W × U) where
  toFun z := (z.1 - t z.2, z.2)
  invFun z := (z.1 + t z.2, z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' x y := by ext <;> simp [map_add, sub_add_sub_comm]
  map_smul' a x := by ext <;> simp [map_smul, smul_sub]

private theorem exists_dual_isometry (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (W : Submodule K V)
    (hW : ∀ w ∈ W, Q w = 0) (n : ℕ)
    (hVdim : finrank K V = 2 * n) (hWdim : finrank K W = n) :
    ∃ U : Submodule K V, finrank K U = n ∧
      Nonempty (Q.IsometryEquiv (QuadraticForm.dualProd K U)) := by
  obtain ⟨U, hU⟩ := W.exists_isCompl
  have hUdim : finrank K U = n := by
    have hd := Submodule.finrank_add_eq_of_isCompl hU
    omega
  let g : W →ₗ[K] Module.Dual K U :=
    Q.polarBilin.compl₁₂ W.subtype U.subtype
  have hWW (w w' : W) : Q.polarBilin w w' = 0 := by
    change Q ((w : V) + w') - Q w - Q w' = 0
    rw [hW _ (W.add_mem w.prop w'.prop), hW _ w.prop, hW _ w'.prop]
    simp
  -- Vanishing against the complement and the singular plane means vanishing everywhere.
  have hginj : Function.Injective g := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    apply Subtype.ext
    apply hQ.1 w
    intro v
    obtain ⟨⟨a, b⟩, rfl⟩ := (W.prodEquivOfIsCompl U hU).surjective v
    change Q.polarBilin w ((a : V) + b) = 0
    rw [map_add, hWW]
    have hb : Q.polarBilin w b = 0 := LinearMap.congr_fun hw b
    rw [hb, zero_add]
  let e : W ≃ₗ[K] Module.Dual K U := g.linearEquivOfInjective hginj (by
    rw [Subspace.dual_finrank_eq, hUdim, hWdim])
  -- A bilinear representative removes the quadratic term on the complement.
  obtain ⟨A, hA⟩ := LinearMap.BilinMap.toQuadraticMap_surjective (Q.comp U.subtype)
  let t : U →ₗ[K] W := e.symm.toLinearMap.comp A
  have ht (u : U) : Q.polarBilin (t u) u = Q u := by
    change e (e.symm (A u)) u = Q u
    rw [e.apply_symm_apply]
    exact congrArg (fun q : QuadraticForm K U => q u) hA
  let E : (Module.Dual K U × U) ≃ₗ[K] V :=
    ((e.symm.prodCongr (LinearEquiv.refl K U)).trans (shear t)).trans
      (W.prodEquivOfIsCompl U hU)
  have hE (z : Module.Dual K U × U) : Q (E z) = QuadraticForm.dualProd K U z := by
    change Q (((e.symm z.1 - t z.2 : W) : V) + (z.2 : V)) = z.1 z.2
    rw [QuadraticMap.map_add Q, hW _ (e.symm z.1 - t z.2).prop]
    change 0 + Q z.2 + Q.polarBilin ((e.symm z.1 : W) - t z.2 : W) z.2 = _
    rw [Submodule.coe_sub, map_sub, LinearMap.sub_apply, ht]
    have hz : Q.polarBilin (e.symm z.1) z.2 = z.1 z.2 :=
      congrArg (fun f : Module.Dual K U => f z.2) (e.apply_symm_apply z.1)
    rw [hz]
    ring
  exact ⟨U, hUdim, ⟨(show (QuadraticForm.dualProd K U).IsometryEquiv Q from
    { E with map_app' := hE }).symm⟩⟩

end General

/-- The evaluation form in two-dimensional coordinates: `ac + bd`. -/
private def splitForm : QuadraticForm F Space :=
  QuadraticMap.linMulLin
    ((LinearMap.fst F F F).comp (LinearMap.fst F Plane Plane))
    ((LinearMap.fst F F F).comp (LinearMap.snd F Plane Plane)) +
  QuadraticMap.linMulLin
    ((LinearMap.snd F F F).comp (LinearMap.fst F Plane Plane))
    ((LinearMap.snd F F F).comp (LinearMap.snd F Plane Plane))

/-- The columns are the singular vectors
`((1,0),(1,0))`, `((0,1),(0,1))`, `((1,0),(1,1))`, and `((1,1),(0,1))`.
Their only nonzero polar pairings are the first with the third and the second
with the fourth. -/
private def splitEquiv : Space ≃ₗ[F] Space where
  toFun z := ((z.1.1 + z.2.1 + z.2.2, z.1.2 + z.2.2),
    (z.1.1 + z.2.1, z.1.2 + z.2.1 + z.2.2))
  invFun z := ((z.1.2 + z.2.1 + z.2.2, z.1.1 + z.1.2 + z.2.1),
    (z.1.2 + z.2.2, z.1.1 + z.2.1))
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' x y := by ext <;> simp [add_left_comm, add_comm]
  map_smul' a x := by ext <;> simp [mul_add]

private def splitIsometry : splitForm.IsometryEquiv form where
  toLinearEquiv := splitEquiv
  map_app' := by decide +kernel

private def dualCoordinates {V : Type*} [AddCommGroup V] [Module F V]
    (b : Basis (Fin 2) F V) :
    (QuadraticForm.dualProd F V).IsometryEquiv splitForm where
  toLinearEquiv := (b.dualBasis.equivFun.prodCongr b.equivFun).trans
    ((LinearEquiv.finTwoArrow F F).prodCongr (LinearEquiv.finTwoArrow F F))
  map_app' z := by
    change b.dualBasis.equivFun z.1 0 * b.equivFun z.2 0 +
      b.dualBasis.equivFun z.1 1 * b.equivFun z.2 1 = z.1 z.2
    have h : (∑ i, b.dualBasis.equivFun z.1 i * b.equivFun z.2 i) = z.1 z.2 := by
      simp only [Basis.dualBasis_equivFun]
      conv_rhs => rw [← b.sum_equivFun z.2]
      simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
    simpa only [Fin.sum_univ_two] using h

/-- A nondegenerate binary four-space with a totally singular plane has the
standard plus-type form, via an actual linear isometry. -/
theorem nonempty_isometryEquiv_of_totallySingular
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (Q : QuadraticForm F W) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : finrank F W = 4) (U : Submodule F W)
    (hUdim : finrank F U = 2) (hU : ∀ u ∈ U, Q u = 0) :
    Nonempty (Q.IsometryEquiv form) := by
  obtain ⟨V, hVdim, ⟨e⟩⟩ := exists_dual_isometry Q hQ U hU 2 hdim hUdim
  exact ⟨(e.trans (dualCoordinates (finBasisOfFinrankEq F V hVdim))).trans splitIsometry⟩

/-- Intrinsic recognition of the standard plus-type form, using the existence of
a totally singular plane. No coordinate or classification premise is required. -/
theorem nonempty_isometryEquiv_of_plusType
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (Q : QuadraticForm F W) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : finrank F W = 4)
    (hplus : ∃ U : Submodule F W, finrank F U = 2 ∧ ∀ u ∈ U, Q u = 0) :
    Nonempty (Q.IsometryEquiv form) := by
  obtain ⟨U, hUdim, hU⟩ := hplus
  exact nonempty_isometryEquiv_of_totallySingular Q hQ hdim U hUdim hU

end OrthogonalFourBinary
