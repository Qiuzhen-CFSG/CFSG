module
public import Theory.Representation.SL2.BinaryQuadratic.Pair
public import Theory.Representation.SL2.BinaryQuadratic.Forms
public import Theory.Combinatorics.BinaryDegreeFour
public import Theory.Representation.SL2.SteinbergParameters
public import Theory.Representation.QuadraticRefinementDescent
public import Theory.Representation.AbsolutelyIrreducible
public import Theory.Representation.Quotient
public import Mathlib.Algebra.Algebra.ZMod
/-!
# Quadratic refinements for degree-four binary SL₂ actions

The concrete highest-weight classification and its digit-product dimension
formula identify every irreducible degree-four module over an algebraic closure
with two distinct Frobenius factors. Their matrix action preserves the
determinant. Schur's lemma rescales its polar form to the prescribed invariant
bilinear form. A linear retraction of extension-field coefficients then
descends the quadratic form, recovering the original polar form exactly.

Thus absolute irreducibility is a hypothesis about the actual action; no
quadratic structure is inferred from an abstract carrier label. This supplies
the SL₂ module-inspection branch of Aschbacher--Smith G.4.1, printed p.342.
-/

public section
open scoped MatrixGroups TensorProduct
namespace Representation.SL2.BinaryQuadratic
open Representation.SL2.BinaryHermitian
open ClassicalOrthogonal.FourPlusMatrix
variable {K L V : Type*} [Field K] [Finite K] [CharP K 2]
  [Field L] [CharP L 2] [IsAlgClosed L]
  [AddCommGroup V] [Module L V] [FiniteDimensional L V]

theorem exists_pair_equiv (ρ : Representation L SL(2,K) V) [ρ.IsIrreducible]
    (hdim : Module.finrank L V=4) (f : ℕ) (hcard : Nat.card K=2^f) :
    ∃ (e : K →+* L) (s j : ℕ), 0<s ∧
      Nonempty (ρ.Equiv (pair e s j)) := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra (ZMod 2) L := ZMod.algebra L 2
  let e : K →+* L := (IsAlgClosed.lift (R := ZMod 2) (S := K) (M := L)).toRingHom
  obtain ⟨n,⟨φ⟩⟩ := exists_highestWeightSpan_equiv e 2 ρ
  have hn : n.val<2^f := by simpa only [←hcard] using n.isLt
  have hd : (∏ i : Fin f, (n.val / 2^(i:ℕ)%2+1))=4 := by
    rw [←highestWeightSpan_finrank_eq_prod_digits e 2 (by decide) n.val f hcard hn]
    exact φ.toLinearEquiv.finrank_eq.symm.trans hdim
  obtain ⟨j,k,hjk,hkf,hw⟩ := Nat.BinaryDegreeFour.exists_two_bits f n.val hn hd
  let s := k-j
  have hs : 0<s := by dsimp [s]; omega
  have hjs : j+s=k := by dsimp [s]; omega
  have hn' : 2^j+2^(j+s)<Nat.card K := by rw [hjs,←hw]; exact n.isLt
  obtain ⟨ψ⟩ := pair_equiv_highestWeightSpan_of_lt_card e s j hs hn'
  have φ' : ρ.Equiv (highestWeightSpan e (2^j+2^(j+s))).toRepresentation := by
    have he : n.val=2^j+2^(j+s) := by rw [hjs]; exact hw
    rw [←he]
    exact φ
  exact ⟨e,s,j,hs,⟨φ'.trans ψ.symm⟩⟩

theorem exists_quadratic_of_finrank_four (ρ : Representation L SL(2,K) V)
    [ρ.IsIrreducible] (hdim : Module.finrank L V=4)
    (f : ℕ) (hcard : Nat.card K=2^f)
    (B : LinearMap.BilinForm L V) (hBinv : ∀ g v w, B (ρ g v) (ρ g w)=B v w) :
    ∃ Q : QuadraticForm L V, Q.polarBilin=B ∧ ∀ g v, Q (ρ g v)=Q v := by
  obtain ⟨e,s,j,hs,⟨φ⟩⟩ := exists_pair_equiv ρ hdim f hcard
  let Q₀ : QuadraticForm L V := determinantForm.comp φ.toLinearEquiv.toLinearMap
  have hQ₀ (g : SL(2,K)) (v : V) : Q₀ (ρ g v)=Q₀ v := by
    change determinantForm (φ (ρ g v))=determinantForm (φ v)
    have hi := LinearMap.congr_fun (φ.isIntertwining' g) v
    change φ (ρ g v)=pair e s j g (φ v) at hi
    rw [hi]
    exact determinant_invariant e s j g (φ v)
  have hpolar : Q₀.polarBilin=
      LinearMap.BilinForm.congr φ.toLinearEquiv.symm (determinantForm (F := L)).polarBilin := by
    change (determinantForm.comp φ.toLinearEquiv.toLinearMap).polarBilin=_
    rw [QuadraticMap.polarBilin_comp]
    rfl
  have hnd : Q₀.polarBilin.Nondegenerate := by
    rw [hpolar]
    exact LinearMap.BilinForm.Nondegenerate.congr φ.toLinearEquiv.symm determinant_polar_nondegenerate
  have hpolarInv (g : SL(2,K)) (v w : V) :
      Q₀.polarBilin (ρ g v) (ρ g w)=Q₀.polarBilin v w := by
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar]
    rw [←map_add,hQ₀,hQ₀,hQ₀]
  obtain ⟨c,hc⟩ := invariant_form_scalar ρ Q₀.polarBilin hnd hpolarInv B hBinv
  refine ⟨c•Q₀,?_,?_⟩
  · rw [hc]
    ext v w
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
      smul_apply,LinearMap.smul_apply,smul_eq_mul]
    ring
  · intro g v
    change c•Q₀ (ρ g v)=c•Q₀ v
    rw [hQ₀]
end Representation.SL2.BinaryQuadratic

namespace Representation.SL2.BinaryQuadratic
variable {F K V : Type*} [Field F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem exists_quadratic_of_absolutelyIrreducible
    (ρ : Representation F SL(2,K) V) [ρ.IsAbsolutelyIrreducible]
    (hdim : Module.finrank F V=4) (f : ℕ) (hcard : Nat.card K=2^f)
    (B : LinearMap.BilinForm F V) (hBinv : ∀ g v w, B (ρ g v) (ρ g w)=B v w) :
    ∃ Q : QuadraticForm F V, Q.polarBilin=B ∧ ∀ g v, Q (ρ g v)=Q v := by
  let L := AlgebraicClosure F
  let : CharP L 2 := charP_of_injective_algebraMap (algebraMap F L).injective 2
  let : (extendScalars L ρ).IsIrreducible :=
    IsAbsolutelyIrreducible.irreducible_of_closure
  have hd : Module.finrank L (L ⊗[F] V)=4 := by
    rw [Module.finrank_baseChange,hdim]
  have hB (g : SL(2,K)) (v w : L ⊗[F] V) :
      B.baseChange L (extendScalars L ρ g v) (extendScalars L ρ g w)=B.baseChange L v w := by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul c v =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul d w => simp only [extendScalars_apply,LinearMap.baseChange_tmul,
          LinearMap.BilinForm.baseChange_tmul,hBinv]
      | add w x hw hx => simp only [map_add,hw,hx]
    | add v x hv hx => simp only [map_add,LinearMap.add_apply,hv,hx]
  obtain ⟨Q,hpolar,hQ⟩ := exists_quadratic_of_finrank_four (extendScalars L ρ)
    hd f hcard (B.baseChange L) hB
  exact QuadraticRefinement.exists_of_extendScalars ρ B Q hQ hpolar
end Representation.SL2.BinaryQuadratic

namespace Representation.SL2.BinaryQuadratic
variable {F K H V : Type*} [Field F] [CharP F 2] [Field K] [Finite K] [CharP K 2]
    [Group H] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem exists_quadratic_of_equiv_sl2 (ρ : Representation F H V)
    [ρ.IsAbsolutelyIrreducible] (hdim : Module.finrank F V=4)
    (e : H≃*SL(2,K)) (f : ℕ) (hcard : Nat.card K=2^f)
    (B : LinearMap.BilinForm F V) (hBinv : ∀ g v w,B (ρ g v) (ρ g w)=B v w) :
    ∃ Q : QuadraticForm F V,Q.polarBilin=B ∧ ∀ g v,Q (ρ g v)=Q v := by
  let σ : Representation F SL(2,K) V := ρ.comp e.symm.toMonoidHom
  let : σ.IsAbsolutelyIrreducible := by
    constructor
    let hρ : (extendScalars (AlgebraicClosure F) ρ).IsIrreducible :=
      IsAbsolutelyIrreducible.irreducible_of_closure
    exact (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (extendScalars (AlgebraicClosure F) ρ)).mpr hρ
  obtain ⟨Q,hpolar,hQ⟩ := exists_quadratic_of_absolutelyIrreducible σ hdim f hcard B
    (fun g => hBinv (e.symm g))
  refine ⟨Q,hpolar,fun g v=>?_⟩
  simpa only [σ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply]
    using hQ (e g) v
end Representation.SL2.BinaryQuadratic
