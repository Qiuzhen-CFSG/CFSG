module

public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_8_k1_one_mem
public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_8_k1_mul_mem
public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_8_k1_inv_mem
public import Theory.GroupTheory.PrimaryClosureKernel

/-!
# Characteristic-primary closure in GLS3, Theorem 2.1.8

For the fixed-point subgroup `Kfix` and the central-defect subgroup `K₁`, let
the defect homomorphism `φ : K₁ → Z` have kernel `Kfix`.  If the central
closed subgroup `Z` lies in a torus `T`, then it has no nontrivial elements of
order a power of the field characteristic: the `r ^ a` power map on `T` is
injective.  The generic kernel-transfer theorem therefore puts every
`r`-power-order element of `K₁` in `Kfix`, and the generated closures agree.

This is the final finite-group step in the proof of GLS3, Theorem 2.1.8.  The
source phrases it as the chain `Kfix ◁ Kfix Z ◁ K₁`, whose quotients are
sections of the semisimple center and hence have order prime to `r`.  The
commutator homomorphism combines those two quotient steps into one kernel
calculation; containment of the center in a maximal torus supplies the same
prime-to-characteristic conclusion.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The characteristic-primary generated subgroups of `K₁` and the fixed
subgroup agree once the central target is contained in a torus and the
central-defect homomorphism has the fixed subgroup as kernel. -/
public theorem theorem_2_1_8_r_primary_closure
    {K : Variety k} [AlgebraicGroup K]
    {r : ℕ} [Fact r.Prime] [CharP k r]
    (σ : AlgebraicGroup.Morphism K K)
    (Z T : ClosedSubgroup K)
    (hZ : Z.toSubgroup ≤ Subgroup.center (Variety.Point K))
    (hT : IsSubtorus T) (hZT : Z ≤ T) :
    let G := Variety.Point K
    let Kfix : Subgroup G :=
      { carrier := {g | σ.onPoints g = g}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          change σ.onPoints (a * b) = a * b
          rw [map_mul, ha, hb]
        inv_mem' := by
          intro a ha
          change σ.onPoints a⁻¹ = a⁻¹
          rw [map_inv, ha] }
    let K₁ : Subgroup G :=
      { carrier := {g | g⁻¹ * σ.onPoints g ∈ Z.toSubgroup}
        one_mem' := theorem_2_1_8_k1_one_mem σ Z
        mul_mem' := by
          intro a b ha hb
          exact theorem_2_1_8_k1_mul_mem σ Z hZ ha hb
        inv_mem' := by
          intro a ha
          exact theorem_2_1_8_k1_inv_mem σ Z hZ ha }
    (φ : K₁ →* Z.toSubgroup) →
    φ.ker = Kfix.subgroupOf K₁ →
    (Subgroup.closure
        {g : G | g ∈ K₁ ∧ ∃ a : ℕ, orderOf g = r ^ a}) =
      Subgroup.closure
        {g : G | g ∈ Kfix ∧ ∃ a : ℕ, orderOf g = r ^ a} := by
  dsimp only
  let Kfix : Subgroup (Variety.Point K) :=
    { carrier := {g | σ.onPoints g = g}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change σ.onPoints (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := by
        intro a ha
        change σ.onPoints a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  let K₁ : Subgroup (Variety.Point K) :=
    { carrier := {g | g⁻¹ * σ.onPoints g ∈ Z.toSubgroup}
      one_mem' := theorem_2_1_8_k1_one_mem σ Z
      mul_mem' := theorem_2_1_8_k1_mul_mem σ Z hZ
      inv_mem' := theorem_2_1_8_k1_inv_mem σ Z hZ }
  intro φ hker
  apply Subgroup.closure_primePowerOrder_eq_of_ker_of_pow_eq_one
    Kfix K₁ (p := r) (H := Z.toSubgroup) _ φ hker
  · intro z a hz
    let zT : Variety.Point T.carrierVariety :=
      T.pointEquiv.symm ⟨(z : Variety.Point K), hZT z.property⟩
    have hzincl : T.inclusion.onPoints zT = (z : Variety.Point K) := by
      change (T.pointEquiv zT).val = (z : Variety.Point K)
      simp [zT]
    have hzambient : (z : Variety.Point K) ^ r ^ a = 1 := by
      exact congrArg Subtype.val hz
    have hzTpow : zT ^ r ^ a = 1 := by
      apply T.inclusion_injective
      rw [map_pow, map_one, hzincl]
      exact hzambient
    have hzTone : zT = 1 :=
      (IsTorus.pow_primePower_bijective hT r a).1
        (by simpa only [one_pow] using hzTpow)
    apply Subtype.ext
    calc
      (z : Variety.Point K) = T.inclusion.onPoints zT := hzincl.symm
      _ = T.inclusion.onPoints 1 := congrArg T.inclusion.onPoints hzTone
      _ = 1 := map_one T.inclusion.onPoints
  · intro g hg
    change g⁻¹ * σ.onPoints g ∈ Z.toSubgroup
    rw [hg]
    simp

end Theory.AlgebraicGroup
