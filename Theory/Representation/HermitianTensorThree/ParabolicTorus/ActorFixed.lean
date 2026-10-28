module
public import Theory.Representation.FiniteFieldSemilinearInvariantFixed
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.LargeFixed
public import Theory.Representation.HermitianTensorThree.UnipotentRadicals
public import Theory.Representation.BinaryOffender.CentralSectionAction

/-!
# Removing coefficients on a saturated actor's fixed space

An inner elementary actor fixes a subspace over the actual fixed field.
Its binary normalizer preserves that space. If it has binary dimension
4n, an odd normalizer with fixed binary dimension greater than 2n has trivial coefficient
action: a nontrivial odd coefficient order is at least three, whereas the
restricted semilinear fixed-space estimate bounds it by less than two.

This removes the coefficient issue at fixed rank exactly 3n in the
endpoint of Aschbacher–Smith 8.2.3 and H.4.4(4), printed pp.716 and381.
The two-by-two congruence calculation is separate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module Subgroup Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ParabolicTorus
namespace Representation.HermitianTensorThree.ParabolicTorus
variable (n : ℕ) [NeZero n]

/-- The inner actor fixed space retains the literal fixed-field scalars. -/
def innerFixed (A : Subgroup (BinaryAut n)) (hA : A ≤ binaryImage n) :
    Submodule (F n) (Space n) where
  carrier := fixedSpace (UnipotentRadicals.ambientAction n) A
  zero_mem' := (fixedSpace _ _).zero_mem
  add_mem' := (fixedSpace _ _).add_mem
  smul_mem' := by
    intro c v hv a
    obtain ⟨g,hg⟩ := hA a.property
    change a.val (c • v) = c • v
    rw [←hg]
    change action n g (c • v) = c • v
    rw [map_smul]
    congr 1
    change binaryActionHom n g v = v
    rw [hg]
    exact hv a

/-- An odd normalizer fixing more than half of the actor fixed space
has trivial coefficient action. This includes the endpoint fixed rank 3n. -/
theorem linear_of_large_fixed_inside_actor
    (A : Subgroup (BinaryAut n)) (hA : A ≤ binaryImage n)
    (ha : Module.finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction n) A) = 4*n)
    (x : BinaryAut n) (hx : x ∈ binaryNormalizer n) (ho : Odd (orderOf x))
    (hn : x ∈ normalizer (A : Set (BinaryAut n)))
    (hle : fixedSpace (UnipotentRadicals.ambientAction n) (zpowers x) ≤
      fixedSpace (UnipotentRadicals.ambientAction n) A)
    (hlarge : 2*n < Module.finrank (ZMod 2)
      (fixedSpace (UnipotentRadicals.ambientAction n) (zpowers x))) :
    IsFixedFieldLinear n x := by
  obtain ⟨τ,hτ⟩ := normalizer_semilinear_of_scalarCentralizer n (scalarCentralizerCoverage n) x hx
  let σ : F n ≃ₐ[ZMod 2] F n := AlgEquiv.ofRingEquiv (f := τ) (fun a => by
    exact congrArg (fun (f : ZMod 2 →+* F n) => f a)
      (Subsingleton.elim (τ.toRingHom.comp (algebraMap (ZMod 2) (F n)))
        (algebraMap (ZMod 2) (F n))))
  let : Module (ZMod 2) (F n) := Algebra.toModule
  let : SMul (ZMod 2) (F n) := (Algebra.toModule : Module (ZMod 2) (F n)).toSMul
  let : SMul (ZMod 2) (Space n) := (binaryModule n).toSMul
  let : SMul (F n) (Space n) := (inferInstance : Module (F n) (Space n)).toSMul
  let := ZMod.instIsScalarTower 2 (F n) (Space n)
  let U := innerFixed n A hA
  have hU : U.restrictScalars (ZMod 2) = fixedSpace (UnipotentRadicals.ambientAction n) A := rfl
  have hd : finrank (ZMod 2) (F n) * finrank (F n) U = 4*n := by
    rw [Module.finrank_mul_finrank]
    have hh := ((Submodule.restrictScalarsEquiv (ZMod 2) (F n) (Space n) U).restrictScalars (ZMod 2)).finrank_eq
    rw [←hh,hU,ha]
  have hs : zpowers x ≤ subspaceStabilizer (UnipotentRadicals.ambientAction n) (U.restrictScalars (ZMod 2)) := by
    rw [hU]
    exact fixedSpace_stable_of_normalizes _ (zpowers_le.mpr hn)
  have hb := FiniteFieldSemilinearDisplacement.fixedSpace_order_bound_on_invariant
    (UnipotentRadicals.ambientAction n) x σ hτ U hs (hU ▸ hle)
  rw [hd] at hb
  let : Nontrivial (Space n) := Module.finrank_pos_iff.mp (by rw [finrank_space]; decide)
  have hod := ho.of_dvd_nat (FiniteFieldSemilinearDisplacement.coefficient_order_dvd
    (UnipotentRadicals.ambientAction n) x σ hτ)
  have hσ : σ = 1 := by
    by_contra hne
    have hne1 : orderOf σ ≠ 1 := fun hh => hne (orderOf_eq_one_iff.mp hh)
    have hthree : 3 ≤ orderOf σ := by obtain ⟨l,hl⟩ := hod; omega
    have hmul := Nat.mul_le_mul_right
      (finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction n) (zpowers x))) hthree
    omega
  intro a v
  have hh := hτ a v
  change x (a • v) = σ a • x v at hh
  simpa only [hσ,AlgEquiv.one_apply] using hh
end Representation.HermitianTensorThree.ParabolicTorus

end
