module

public import Theory.SpecificGroups.Monster.Construction.LocalC.SourceNormalizer.Orientation.QuarterTurnGeneration.CentralAction
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Forms
public import Mathlib.LinearAlgebra.QuadraticForm.Basis
public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Hyperbolic coordinates for the central square form

The polar pairing identifies a half-dimensional totally singular subspace with
the dual of any complementary subspace. A bilinear representative of the
quadratic form on the complement supplies a linear shear making that complement
singular. This constructs an isometry to the evaluation form `q(f,u) = f(u)`;
a basis then identifies it with the standard split form.

We apply this construction to the actual central quotient of `Q1Image`, with
its intrinsic square form and its proved 12-dimensional singular subspace.
Thus the twisted addition of the source coordinates is preserved. Finally,
each standard basis vector is a difference of two nonsingular vectors, using
a distinct hyperbolic pair, and the isometry transports this spanning result.

Source: Aschbacher, *Sporadic Groups*, Exercise 4.6, p. 64, and Section 27,
pp. 144–145. This supplies the hyperbolic geometry used by Exercise 4.4 and the
normalizer construction on pp. 147–148.
-/

public section
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Sporadic.Monster.Construction.LocalC.SourceNormalizer
open TrialitySpin Atlas.Codes

namespace HyperbolicModel
section General
open Module
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

private def shear {W U : Type*} [AddCommGroup W] [Module F W]
    [AddCommGroup U] [Module F U] (t : U →ₗ[F] W) : (W × U) ≃ₗ[F] (W × U) where
  toFun z := (z.1 - t z.2, z.2)
  invFun z := (z.1 + t z.2, z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' x y := by ext <;> simp [map_add, sub_add_sub_comm]
  map_smul' a x := by ext <;> simp [map_smul, smul_sub]

private theorem exists_dual_isometry (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) (W : Submodule F V)
    (hW : ∀ w ∈ W, Q w = 0) (n : ℕ)
    (hVdim : finrank F V = 2*n) (hWdim : finrank F W = n) :
    ∃ U : Submodule F V, finrank F U = n ∧
      Nonempty (Q.IsometryEquiv (QuadraticForm.dualProd F U)) := by
  obtain ⟨U,hU⟩ := W.exists_isCompl
  have hUdim : finrank F U = n := by
    have hd := Submodule.finrank_add_eq_of_isCompl hU
    omega
  let g : W →ₗ[F] Module.Dual F U :=
    Q.polarBilin.compl₁₂ W.subtype U.subtype
  have hWW (w w' : W) : Q.polarBilin w w' = 0 := by
    change Q ((w : V) + w') - Q w - Q w' = 0
    rw [hW _ (W.add_mem w.prop w'.prop),hW _ w.prop,hW _ w'.prop]
    simp
  have hginj : Function.Injective g := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    apply Subtype.ext
    apply hQ.1 w
    intro v
    obtain ⟨⟨a,b⟩,rfl⟩ := (W.prodEquivOfIsCompl U hU).surjective v
    change Q.polarBilin w ((a : V) + b) = 0
    rw [map_add,hWW]
    have hb : Q.polarBilin w b = 0 := LinearMap.congr_fun hw b
    rw [hb,zero_add]
  let e : W ≃ₗ[F] Module.Dual F U := g.linearEquivOfInjective hginj (by
    rw [Subspace.dual_finrank_eq,hUdim,hWdim])
  obtain ⟨A,hA⟩ := LinearMap.BilinMap.toQuadraticMap_surjective (Q.comp U.subtype)
  let t : U →ₗ[F] W := e.symm.toLinearMap.comp A
  have ht (u : U) : Q.polarBilin (t u) u = Q u := by
    change e (e.symm (A u)) u = Q u
    rw [e.apply_symm_apply]
    exact congrArg (fun q : QuadraticForm F U => q u) hA
  let E : (Module.Dual F U × U) ≃ₗ[F] V :=
    ((e.symm.prodCongr (LinearEquiv.refl F U)).trans (shear t)).trans
      (W.prodEquivOfIsCompl U hU)
  have hE (z : Module.Dual F U × U) : Q (E z) = QuadraticForm.dualProd F U z := by
    change Q (((e.symm z.1 - t z.2 : W) : V) + (z.2 : V)) = z.1 z.2
    rw [QuadraticMap.map_add Q,hW _ (e.symm z.1 - t z.2).prop]
    change 0 + Q z.2 + Q.polarBilin ((e.symm z.1 : W) - t z.2 : W) z.2 = _
    rw [Submodule.coe_sub, map_sub, LinearMap.sub_apply, ht]
    have hz : Q.polarBilin (e.symm z.1) z.2 = z.1 z.2 :=
      congrArg (fun f : Module.Dual F U => f z.2) (e.apply_symm_apply z.1)
    rw [hz]
    ring
  exact ⟨U,hUdim,⟨(show (QuadraticForm.dualProd F U).IsometryEquiv Q from
    { E with map_app' := hE }).symm⟩⟩

/-- Evaluation in a basis is the split coordinate form. -/
private def dual_isometry (n : ℕ) (b : Basis (Fin n) F V) :
    (QuadraticForm.dualProd F V).IsometryEquiv (ClassicalOrthogonal.formD n F) where
  toLinearEquiv := (b.dualBasis.equivFun.prodCongr b.equivFun).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin n) F F).symm
  map_app' z := by
    rw [ClassicalOrthogonal.formD_apply]
    change (∑ i, b.dualBasis.equivFun z.1 i * b.equivFun z.2 i) = z.1 z.2
    simp only [Basis.dualBasis_equivFun]
    conv_rhs => rw [← b.sum_equivFun z.2]
    simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

private theorem exists_split_isometry (Q : QuadraticForm F V)
    (hQ : Q.polarBilin.Nondegenerate) (W : Submodule F V)
    (hW : ∀ w ∈ W, Q w = 0) (n : ℕ)
    (hVdim : finrank F V = 2*n) (hWdim : finrank F W = n) :
    Nonempty (Q.IsometryEquiv (ClassicalOrthogonal.formD n F)) := by
  obtain ⟨U,hUdim,⟨e⟩⟩ := exists_dual_isometry Q hQ W hW n hVdim hWdim
  exact ⟨e.trans (dual_isometry n (finBasisOfFinrankEq F U hUdim))⟩
end General

open ClassicalOrthogonal
private abbrev K := ZMod 2

private theorem unit_in_span (a : Index 12) :
    Pi.single a (1 : K) ∈ Submodule.span K {v : VectorD 12 K | formD 12 K v = 1} := by
  classical
  let S := Submodule.span K {v : VectorD 12 K | formD 12 K v = 1}
  have H (i : Fin 12) (j : Fin 12) (hij : i ≠ j) (a : Index 12)
      (ha : a = .inl i ∨ a = .inr i) : Pi.single a (1 : K) ∈ S := by
    let z : VectorD 12 K := Pi.single (.inl j) 1 + Pi.single (.inr j) 1
    have hz : formD 12 K z = 1 := by
      simp [formD_apply,z,Pi.single_apply]
    have hza : formD 12 K (z + Pi.single a 1) = 1 := by
      rcases ha with rfl | rfl <;>
        simp [formD_apply,z,Pi.single_apply,mul_add,
          Finset.sum_add_distrib,hij,hij.symm]
    have hmem := S.sub_mem (Submodule.subset_span hza) (Submodule.subset_span hz)
    simpa only [add_sub_cancel_left] using hmem
  rcases a with i | i
  · obtain ⟨j,hji⟩ := exists_ne i
    exact H i j hji.symm (.inl i) (Or.inl rfl)
  · obtain ⟨j,hji⟩ := exists_ne i
    exact H i j hji.symm (.inr i) (Or.inr rfl)

private theorem nonsingular_span :
    Submodule.span K {v : VectorD 12 K | formD 12 K v = 1} = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun K (Index 12)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨a,rfl⟩
  rw [Pi.basisFun_apply]
  exact unit_in_span a
end HyperbolicModel

/-- The actual central square form is the orthogonal sum of twelve hyperbolic planes.
The construction uses the intrinsic quotient addition throughout. -/
def q1CentralHyperbolicIsometry :
    q1CentralQuadraticForm.IsometryEquiv (ClassicalOrthogonal.formD 12 (ZMod 2)) :=
  Classical.choice (HyperbolicModel.exists_split_isometry q1CentralQuadraticForm
    q1CentralQuadraticForm_nonsingular q1CentralSingularSubspace
    q1CentralSingularSubspace_totallySingular 12
    q1CentralQuotient_finrank q1CentralSingularSubspace_finrank)

/-- Nonsingular vectors span the actual extraspecial central quotient. -/
theorem q1CentralQuadraticForm_nonsingular_span :
    Submodule.span Bit {v : CentralSpace | q1CentralQuadraticForm v = 1} = ⊤ := by
  let e := q1CentralHyperbolicIsometry
  have hi : e.symm '' {v | ClassicalOrthogonal.formD 12 (ZMod 2) v = 1} =
      {v : CentralSpace | q1CentralQuadraticForm v = 1} := by
    ext v
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact (e.symm.map_app w).trans hw
    · intro hv
      exact ⟨e v,(e.map_app v).trans hv,e.symm_apply_apply v⟩
  have hs := congrArg (Submodule.map e.symm.toLinearEquiv.toLinearMap)
    HyperbolicModel.nonsingular_span
  rw [Submodule.map_span] at hs
  change Submodule.span Bit (e.symm '' {v | ClassicalOrthogonal.formD 12 (ZMod 2) v = 1}) = _ at hs
  rw [hi,Submodule.map_top,LinearMap.range_eq_top.mpr e.symm.surjective] at hs
  exact hs
end Sporadic.Monster.Construction.LocalC.SourceNormalizer
