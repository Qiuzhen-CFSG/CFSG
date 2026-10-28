module

public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_8_n_normal
public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_8_l_normal
public import Theory.AlgebraicGroup.Automorphisms.Lang.theorem_2_1_8_r_primary_closure

/-!
This module isolates `theorem_2_1_8` from `Theory.AlgebraicGroup.Automorphisms.Lang`.
It retains the declarations following that unresolved result up to the next
unresolved result, preserving the source order and public API of the GLS3
algebraic-group development.

The six preceding obligation modules expose the exact subgroup fields,
normality facts, and characteristic-primary closure transfer needed by the
theorem's dependent `let` construction.
-/

universe u v

set_option warningAsError false

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public theorem theorem_2_1_8
    {K : Variety k} [AlgebraicGroup K]
    {r : ℕ} [Fact r.Prime] [CharP k r]
    (σ : AlgebraicGroup.Morphism K K)
    (hσ : IsAlgebraicSteinbergEndomorphism σ)
    (hK : IsSemisimpleAlgebraicGroup K)
    (Z : ClosedSubgroup K)
    (hZ : Z.toSubgroup ≤ Subgroup.center (Variety.Point K))
    (hZσ : σ.onPoints '' (Z : Set (Variety.Point K)) =
      (Z : Set (Variety.Point K))) :
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
    let N := Kfix ⊔ Z.toSubgroup
    let comm : Z.toSubgroup → Z.toSubgroup := fun z =>
      ⟨(z : G)⁻¹ * σ.onPoints (z : G), by
        have hzσ : σ.onPoints (z : G) ∈ Z.toSubgroup := by
          change σ.onPoints (z : G) ∈ (Z : Set (Variety.Point K))
          rw [← hZσ]
          exact ⟨(z : G), z.property, rfl⟩
        exact Z.toSubgroup.mul_mem
          (Z.toSubgroup.inv_mem z.property) hzσ⟩
    let L : Subgroup Z.toSubgroup := Subgroup.closure (Set.range comm)
    let : (N.subgroupOf K₁).Normal := theorem_2_1_8_n_normal σ Z hZ
    let : L.Normal := theorem_2_1_8_l_normal Z hZ comm
    (∃ φ : K₁ →* Z.toSubgroup,
      (∀ g : K₁, (φ g : G) = (g : G)⁻¹ * σ.onPoints (g : G)) ∧
      Function.Surjective φ ∧
      φ.ker = Kfix.subgroupOf K₁ ∧
      (∃ e : K₁ ⧸ N.subgroupOf K₁ ≃* Z.toSubgroup ⧸ L,
        ∀ g : K₁,
          e (QuotientGroup.mk' (N.subgroupOf K₁) g) =
            QuotientGroup.mk' L (φ g))) ∧
    (∀ T : ClosedSubgroup K,
      IsMaximalTorus T →
      σ.onPoints '' (T : Set G) = T →
      (K₁ : Set G) =
        {g : G | ∃ k ∈ Kfix, ∃ t ∈ T.toSubgroup, t ∈ K₁ ∧ g = k * t}) ∧
    (Subgroup.closure
        {g : G | g ∈ K₁ ∧ ∃ a : ℕ, orderOf g = r ^ a}) =
      Subgroup.closure
        {g : G | g ∈ Kfix ∧ ∃ a : ℕ, orderOf g = r ^ a} := by
  sorry

end Theory.AlgebraicGroup
