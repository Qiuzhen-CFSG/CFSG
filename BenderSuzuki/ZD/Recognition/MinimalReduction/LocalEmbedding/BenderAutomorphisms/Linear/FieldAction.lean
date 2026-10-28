module

public import BenderSuzuki.Converse.PSL2
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Concrete field automorphisms of binary PSL₂

In characteristic two the actual quotient map SL₂ → PSL₂ is an isomorphism.
Applying a field automorphism entrywise and transporting through that map
therefore defines a field automorphism of the projective group. The formula
on quotient representatives fixes the matrix convention used by the
semilinear-coverage and fixed-field descent arguments.

This file constructs the action only. It does not assert that arbitrary
abstract automorphisms are semilinear, nor that outer involutions are conjugate
to field automorphisms. Those are separate inputs needed for GLS, Volume 4,
Chapter 4, Lemma 3.4(c).
-/

namespace BenderSuzuki.ZD.Linear
open _root_.BenderSuzuki.MatrixGroups

@[expose] public noncomputable def sl2QuotientEquiv (K : Type*) [Field K] [CharP K 2] :
    Matrix.SpecialLinearGroup (Fin 2) K ≃* PSL2MatrixGroup K :=
  MulEquiv.ofBijective (Converse.pi K) ⟨Converse.pi_injective, Converse.pi_surjective⟩

@[expose] public def sl2FieldAut {K : Type*} [Field K] (σ : K ≃+* K) :
    MulAut (Matrix.SpecialLinearGroup (Fin 2) K) where
  toFun := Matrix.SpecialLinearGroup.map σ.toRingHom
  invFun := Matrix.SpecialLinearGroup.map σ.symm.toRingHom
  left_inv g := by ext i j; exact σ.symm_apply_apply (g i j)
  right_inv g := by ext i j; exact σ.apply_symm_apply (g i j)
  map_mul' := (Matrix.SpecialLinearGroup.map σ.toRingHom).map_mul

@[expose] public noncomputable def fieldAut {K : Type*} [Field K] [CharP K 2] (σ : K ≃+* K) :
    MulAut (PSL2MatrixGroup K) :=
  MulAut.congr (sl2QuotientEquiv K) (sl2FieldAut σ)

public theorem fieldAut_apply_pi {K : Type*} [Field K] [CharP K 2] (σ : K ≃+* K)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    fieldAut σ (Converse.pi K g) =
      Converse.pi K (Matrix.SpecialLinearGroup.map σ.toRingHom g) := by
  change sl2QuotientEquiv K (sl2FieldAut σ
    ((sl2QuotientEquiv K).symm (sl2QuotientEquiv K g))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl
end BenderSuzuki.ZD.Linear
