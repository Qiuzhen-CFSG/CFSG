module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# Coordinates for a semilinear point stabilizer

The ambient group acts only as permutations of a field. Scalar multiplication
embeds its unit group in the stabilizer of zero. The subgroup fixing both zero
and one embeds in the field automorphism group, and every zero stabilizer
element has a unique scalar-times-two-point-stabilizer decomposition.

These are the groups K and Γ in GLS, Volume 4, Chapter 1, Theorem 3.2
(`refs/KGroup/GLS4/Chapter1.tex`, following line 305). The coordinates alone
do not assert the classification of the ambient permutation group.
-/

@[expose] public section

namespace MulAction.SemilinearPointStabilizer

variable {X F : Type*} [Group X] [Field F] [MulAction X F]

/-- The two coordinate assumptions on the zero stabilizer. The action of the
whole group is not assumed to preserve any field operations. -/
structure Coordinates (X F : Type*) [Group X] [Field F] [MulAction X F] : Prop where
  scalars : ∀ a : Fˣ, ∃ g : X, ∀ x : F, g • x = (a : F) * x
  semilinear : ∀ g : X, g • (0 : F) = 0 →
    ∃ a : Fˣ, ∃ σ : F ≃+* F, ∀ x : F, g • x = (a : F) * σ x

/-- The literal subgroup fixing the two distinguished field elements. -/
def twoPoint : Subgroup X := stabilizer X (0 : F) ⊓ stabilizer X (1 : F)

namespace Coordinates

variable [FaithfulSMul X F] (c : Coordinates X F)

include c

/-- Scalar multiplication, realized inside the original acting group. -/
noncomputable def scalar : Fˣ →* X where
  toFun a := Classical.choose (c.scalars a)
  map_one' := by
    apply eq_of_smul_eq_smul (α := F)
    intro x
    simpa using Classical.choose_spec (c.scalars 1) x
  map_mul' a b := by
    apply eq_of_smul_eq_smul (α := F)
    intro x
    rw [Classical.choose_spec (c.scalars (a * b)), mul_smul,
      Classical.choose_spec (c.scalars b), Classical.choose_spec (c.scalars a)]
    exact mul_assoc (a : F) (b : F) x

@[simp] theorem scalar_smul (a : Fˣ) (x : F) :
    c.scalar a • x = (a : F) * x := Classical.choose_spec (c.scalars a) x

theorem scalar_injective : Function.Injective c.scalar := by
  intro a b hab
  apply Units.ext
  have h := congrArg (fun g : X => g • (1 : F)) hab
  simpa using h

/-- The scalar subgroup K in the source. -/
noncomputable def scalarSubgroup : Subgroup X := c.scalar.range

theorem scalarSubgroup_le_stabilizer : c.scalarSubgroup ≤ stabilizer X (0 : F) := by
  rintro g ⟨a, rfl⟩
  simp [mem_stabilizer_iff]

theorem scalar_fixed_iff (a : Fˣ) (ha : a ≠ 1) (x : F) :
    c.scalar a • x = x ↔ x = 0 := by
  rw [scalar_smul]
  have hne : (a : F) - 1 ≠ 0 := by
    intro h
    exact ha (Units.ext (sub_eq_zero.mp h))
  constructor
  · intro hx
    have hz : ((a : F) - 1) * x = 0 := by rw [sub_mul, one_mul, hx, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left hne
  · rintro rfl
    simp

omit [FaithfulSMul X F] in
/-- A two-point stabilizer element acts by a field automorphism. -/
theorem exists_fieldAut (g : twoPoint (X := X) (F := F)) :
    ∃ σ : F ≃+* F, ∀ x : F, (g : X) • x = σ x := by
  obtain ⟨a, σ, hg⟩ := c.semilinear g (mem_stabilizer_iff.mp g.property.1)
  have ha : (a : F) = 1 := by
    simpa using (hg 1).symm.trans (mem_stabilizer_iff.mp g.property.2)
  exact ⟨σ, fun x => by simpa [ha] using hg x⟩

/-- The actual action of Γ on the field, as field automorphisms. -/
noncomputable def fieldAut : twoPoint (X := X) (F := F) →* (F ≃+* F) where
  toFun g := Classical.choose (c.exists_fieldAut g)
  map_one' := by
    ext x
    exact (Classical.choose_spec (c.exists_fieldAut 1) x).symm.trans (one_smul X x)
  map_mul' g h := by
    ext x
    change Classical.choose (c.exists_fieldAut (g * h)) x =
      Classical.choose (c.exists_fieldAut g) (Classical.choose (c.exists_fieldAut h) x)
    rw [← Classical.choose_spec (c.exists_fieldAut (g * h)),
      ← Classical.choose_spec (c.exists_fieldAut h),
      ← Classical.choose_spec (c.exists_fieldAut g)]
    exact mul_smul (g : X) (h : X) x

omit [FaithfulSMul X F] in
@[simp] theorem fieldAut_apply (g : twoPoint (X := X) (F := F)) (x : F) :
    c.fieldAut g x = (g : X) • x := (Classical.choose_spec (c.exists_fieldAut g) x).symm

theorem fieldAut_injective : Function.Injective c.fieldAut := by
  intro g h hgh
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α := F)
  intro x
  simpa using DFunLike.congr_fun hgh x

/-- Multiplication in the original group gives the source factorization KΓ. -/
theorem exists_scalar_mul_twoPoint (g : stabilizer X (0 : F)) :
    ∃ a : Fˣ, ∃ γ : twoPoint (X := X) (F := F), c.scalar a * (γ : X) = g := by
  obtain ⟨a, σ, hg⟩ := c.semilinear g (mem_stabilizer_iff.mp g.property)
  have hγ : (c.scalar a)⁻¹ * (g : X) ∈ twoPoint (X := X) (F := F) := by
    constructor
    · change ((c.scalar a)⁻¹ * (g : X)) • (0 : F) = 0
      rw [mul_smul, mem_stabilizer_iff.mp g.property]
      have hk : c.scalar a • (0 : F) = 0 := by simp
      simpa only [hk] using inv_smul_smul (c.scalar a) (0 : F)
    · change ((c.scalar a)⁻¹ * (g : X)) • (1 : F) = 1
      rw [mul_smul, hg]
      simpa using inv_smul_smul (c.scalar a) (1 : F)
  exact ⟨a, ⟨_, hγ⟩, by simp⟩

/-- The KΓ coordinates are unique. -/
theorem scalar_mul_twoPoint_injective :
    Function.Injective (fun z : Fˣ × twoPoint (X := X) (F := F) =>
      c.scalar z.1 * (z.2 : X)) := by
  rintro ⟨a, γ⟩ ⟨b, δ⟩ h
  have hab : a = b := by
    apply Units.ext
    have h1 := congrArg (fun g : X => g • (1 : F)) h
    simpa only [mul_smul, mem_stabilizer_iff.mp γ.property.2,
      mem_stabilizer_iff.mp δ.property.2, scalar_smul, mul_one] using h1
  subst b
  have hγδ : γ = δ := Subtype.ext (mul_left_cancel h)
  exact Prod.ext rfl hγδ

/-- A type equivalence retaining the literal product map into the stabilizer. -/
noncomputable def stabilizerEquiv :
    (Fˣ × twoPoint (X := X) (F := F)) ≃ stabilizer X (0 : F) :=
  Equiv.ofBijective
    (fun z => ⟨c.scalar z.1 * (z.2 : X), (stabilizer X (0 : F)).mul_mem
      (c.scalarSubgroup_le_stabilizer ⟨z.1, rfl⟩) z.2.property.1⟩)
    ⟨fun _ _ h => c.scalar_mul_twoPoint_injective (congrArg Subtype.val h), by
      intro g
      obtain ⟨a, γ, h⟩ := c.exists_scalar_mul_twoPoint g
      exact ⟨(a, γ), Subtype.ext h⟩⟩

theorem card_stabilizer [Finite F] :
    Nat.card (stabilizer X (0 : F)) = (Nat.card F - 1) *
      Nat.card (twoPoint (X := X) (F := F)) := by
  rw [← Nat.card_congr c.stabilizerEquiv, Nat.card_prod, Nat.card_units]

theorem card_twoPoint_dvd [Finite X] [Finite F] {p n : ℕ}
    (hp : p.Prime) (hF : Nat.card F = p ^ n) :
    Nat.card (twoPoint (X := X) (F := F)) ∣ n := by
  rw [← FiniteField.card_ringAut_of_card_prime_pow hp hF]
  exact Subgroup.card_dvd_of_injective c.fieldAut c.fieldAut_injective

/-- Conjugation by a semilinear element acts on scalars through its field part. -/
theorem conj_scalar (g : X) (a : Fˣ) (σ : F ≃+* F)
    (hg : ∀ x : F, g • x = (a : F) * σ x) (b : Fˣ) :
    g * c.scalar b * g⁻¹ = c.scalar (Units.map σ.toMonoidHom b) := by
  have h : g * c.scalar b = c.scalar (Units.map σ.toMonoidHom b) * g := by
    apply eq_of_smul_eq_smul (α := F)
    intro x
    simp only [mul_smul, scalar_smul, hg, map_mul, Units.coe_map, mul_left_comm]
    rfl
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

/-- K is normalized by the full zero stabilizer, with relative normality
expressed in the original group. -/
theorem stabilizer_le_scalar_normalizer :
    stabilizer X (0 : F) ≤ Subgroup.normalizer c.scalarSubgroup := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg k hk
  obtain ⟨a, σ, hσ⟩ := c.semilinear g (mem_stabilizer_iff.mp hg)
  obtain ⟨b, rfl⟩ := hk
  exact ⟨Units.map σ.toMonoidHom b, (c.conj_scalar g a σ hσ b).symm⟩

/-- Orbit-stabilizer with the actual KΓ coordinates. -/
theorem card_group [Finite F] [IsPretransitive X F] :
    Nat.card X = Nat.card F * (Nat.card F - 1) *
      Nat.card (twoPoint (X := X) (F := F)) := by
  calc
    Nat.card X = Nat.card (stabilizer X (0 : F)) * (stabilizer X (0 : F)).index :=
      (stabilizer X (0 : F)).card_mul_index.symm
    _ = _ := by rw [index_stabilizer_of_transitive, c.card_stabilizer]; ac_rfl

/-- The ambient order divides the full semilinear-stabilizer order. -/
theorem card_group_dvd [Finite X] [Finite F] [IsPretransitive X F]
    {p n : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ n) :
    Nat.card X ∣ p ^ n * (p ^ n - 1) * n := by
  rw [c.card_group, hF]
  exact Nat.mul_dvd_mul_left _ (c.card_twoPoint_dvd hp hF)

end Coordinates

end MulAction.SemilinearPointStabilizer
