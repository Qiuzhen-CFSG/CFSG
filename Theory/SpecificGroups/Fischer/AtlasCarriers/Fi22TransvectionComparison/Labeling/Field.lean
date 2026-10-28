module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.RootWords
public import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Computable coordinates for the Fi22 root comparison

The quadratic field with generator satisfying a² = a + 1 gives an executable
coordinate model. A genuine field equivalence transports its norm and rank-one
transvection formula to the fixed identity-form GF(4)^6 model.

Application: the explicit root labeling for GLS3 Table 5.3t,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

@[expose] public section
open Theory.SpecificGroups
open scoped LinearAlgebra.Projectivization
namespace Sporadic.Fischer.Fi22.TransvectionComparison.Labeling
abbrev Four := QuadraticAlgebra (ZMod 2) 1 1
instance noRoot : Fact (∀ r : ZMod 2, r ^ 2 ≠ 1 + 1 * r) := ⟨by decide +kernel⟩
instance fourFintype : Fintype Four :=
  Fintype.ofEquiv (ZMod 2 × ZMod 2) (QuadraticAlgebra.equivProd 1 1).symm
instance fourCharP : CharP Four 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) Four).injective 2
noncomputable def fieldEquiv : Four ≃+* U6Two.Field := by
  letI := Fintype.ofFinite U6Two.Field
  apply FiniteField.ringEquivOfCardEq
  rw [show Fintype.card Four = 4 by decide +kernel, ← Nat.card_eq_fintype_card,
    U6Two.field_card]
def digit (n : Nat) : Four := ⟨(n % 2 : Nat), (n / 2 % 2 : Nat)⟩
def vector (n : Nat) : Fin 6 → Four := fun k => digit ((n >>> (2 * k.val)) % 4)
def norm (v : Fin 6 → Four) : Four := ∑ k, (v k)^2 * v k
noncomputable def liftVector (v : Fin 6 → Four) : U6Two.Vector := fun k => fieldEquiv (v k)
theorem lift_norm (v : Fin 6 → Four) : U6Two.hermitianNorm (liftVector v) = fieldEquiv (norm v) := by
  simp only [U6Two.hermitianNorm, dotProduct, liftVector, norm,
    U6Two.conjugation_apply, map_sum, map_mul, map_pow]

/-- Six-digit base-four encoding, with the constant coefficient first. -/
def encodeVector (v : Fin 6 → Four) : Nat :=
  ∑ k, ((v k).re.val * 4 ^ k.val + (v k).im.val * (2 * 4 ^ k.val))

def transvection (v w : Fin 6 → Four) : Fin 6 → Four :=
  w + (∑ k, (v k)^2 * w k) • v

/-- Zero or a representative whose first nonzero coordinate is one. -/
def Normalized (v : Fin 6 → Four) : Prop :=
  v = 0 ∨ ∃ k : Fin 6, v k = 1 ∧ ∀ j : Fin 6, j < k → v j = 0

instance (v : Fin 6 → Four) : Decidable (Normalized v) := by
  unfold Normalized
  infer_instance

/-- Transport of the rank-one vector formula to the actual GF(4) model. -/
theorem lift_transvection (v w : Fin 6 → Four) :
    liftVector (transvection v w) =
      liftVector w + ((fun k => U6Two.conjugation (liftVector v k)) ⬝ᵥ
        liftVector w) • liftVector v := by
  funext k
  simp only [liftVector, transvection, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    map_add, map_mul, map_sum, map_pow, U6Two.conjugation_apply, dotProduct]

end Sporadic.Fischer.Fi22.TransvectionComparison.Labeling
