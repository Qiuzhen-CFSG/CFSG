module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.Basic

/-!
# Stabilizer inputs to scalar transfer

The zero stabilizer B is KΓ, with K normal in B and Γ cyclic. Its intrinsic
and ambient commutator subgroups therefore lie in K. The actual coordinate
bijection also gives [B:K] = |Γ|. At binary degree every odd Sylow subgroup
of B is Sylow in the actor, since [X:B] is a power of two.

These are the relative subgroup and index inputs in GLS, Volume 4,
Chapter 1, Lemma 3.9, `refs/KGroup/GLS4/Chapter1.tex`, lines 435–443.
No normality of K in the full actor is assumed.
-/

open scoped IsMulCommutative commutatorElement
namespace MulAction.SemilinearPointStabilizer.Coordinates
variable {X F : Type*} [Group X] [Finite X] [Field F] [MulAction X F] [FaithfulSMul X F]
variable (c : Coordinates X F)

omit [Finite X] in
/-- The commutator inside B lies in the relative scalar subgroup. -/
public theorem commutator_stabilizer_le_scalar [Finite F] :
    commutator (stabilizer X (0 : F)) ≤
      c.scalarSubgroup.subgroupOf (stabilizer X (0 : F)) := by
  let B := stabilizer X (0 : F)
  let K := c.scalarSubgroup.subgroupOf B
  let Γ := twoPoint (X := X) (F := F)
  let H := Γ.subgroupOf B
  have hΓB : Γ ≤ B := inf_le_left
  let : K.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer c.scalarSubgroup_le_stabilizer).mpr
      c.stabilizer_le_scalar_normalizer
  let : IsCyclic Γ := c.twoPoint_isCyclic
  let : IsCyclic H := (Subgroup.subgroupOfEquivOfLe hΓB).isCyclic.mpr inferInstance
  apply Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top (H := H) ?_
    inferInstance
  apply top_unique
  intro g _
  obtain ⟨a, γ, hprod⟩ := c.exists_scalar_mul_twoPoint g
  apply Subgroup.mem_sup_of_normal_left.mpr
  refine ⟨⟨c.scalar a, c.scalarSubgroup_le_stabilizer ⟨a, rfl⟩⟩, ?_,
    ⟨γ, γ.property.1⟩, ?_, ?_⟩
  · exact ⟨a, rfl⟩
  · exact γ.property
  · exact Subtype.ext hprod

/-- The relative scalar index is the order of the literal two-point stabilizer. -/
public theorem scalar_relIndex_stabilizer [Finite F] :
    c.scalarSubgroup.relIndex (stabilizer X (0 : F)) =
      Nat.card (twoPoint (X := X) (F := F)) := by
  have hc : Nat.card (c.scalarSubgroup.subgroupOf (stabilizer X (0 : F))) =
      Nat.card c.scalarSubgroup :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.scalarSubgroup_le_stabilizer).toEquiv
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := c.scalarSubgroup))
  calc
    Nat.card c.scalarSubgroup * c.scalarSubgroup.relIndex (stabilizer X (0 : F)) =
        Nat.card (stabilizer X (0 : F)) := by
      rw [← hc]
      exact (c.scalarSubgroup.subgroupOf (stabilizer X (0 : F))).card_mul_index
    _ = Nat.card c.scalarSubgroup * Nat.card (twoPoint (X := X) (F := F)) := by
      rw [c.card_stabilizer, c.card_scalarSubgroup]

omit [Finite X] in
/-- The commutator word used by the focal generators is scalar. -/
public theorem stabilizer_commutatorElement_mem_scalar [Finite F]
    (x : X) (hx : x ∈ stabilizer X (0 : F))
    (y : X) (hy : y ∈ stabilizer X (0 : F)) :
    x⁻¹ * y * x * y⁻¹ ∈ c.scalarSubgroup := by
  have h := c.commutator_stabilizer_le_scalar
    (Subgroup.commutator_mem_commutator
      (H₁ := ⊤) (H₂ := ⊤)
      (Subgroup.mem_top (⟨x, hx⟩⁻¹ : stabilizer X (0 : F)))
      (Subgroup.mem_top (⟨y, hy⟩ : stabilizer X (0 : F))))
  simpa only [Subgroup.mem_subgroupOf, commutatorElement_def,
    Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] using h

omit [Finite X] in
/-- The ambient image of the stabilizer commutator lies in K. -/
public theorem ambient_stabilizer_commutator_le_scalar [Finite F] :
    ⁅stabilizer X (0 : F), stabilizer X (0 : F)⁆ ≤ c.scalarSubgroup := by
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  simpa only [commutatorElement_def, inv_inv] using
    c.stabilizer_commutatorElement_mem_scalar x⁻¹ ((stabilizer X (0 : F)).inv_mem hx) y hy

omit [FaithfulSMul X F] in
/-- At binary degree an odd Sylow subgroup can be chosen inside B. -/
public theorem exists_sylow_le_stabilizer [Finite F] {n p : ℕ}
    (hp : p.Prime) (hodd : Odd p)
    (htwo : IsMultiplyPretransitive X F 2) (hF : Nat.card F = 2 ^ n) :
    ∃ R : Sylow p X, (R : Subgroup X) ≤ stabilizer X (0 : F) := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsPreprimitive X F := isPreprimitive_of_is_two_pretransitive htwo
  let B := stabilizer X (0 : F)
  let R₀ : Sylow p B := Classical.choice inferInstance
  let R := (R₀ : Subgroup B).map B.subtype
  have hi : ¬ p ∣ B.index := by
    rw [index_stabilizer_of_transitive, hF]
    intro h
    have hp2 : p = 2 :=
      ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h)).resolve_left hp.ne_one
    exact hodd.not_two_dvd_nat (hp2 ▸ dvd_rfl)
  have hRi : ¬ p ∣ R.index := by
    dsimp [R]
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul R₀.not_dvd_index hi
  exact ⟨(R₀.isPGroup'.map B.subtype).toSylow hRi, Subgroup.map_subtype_le _⟩
end MulAction.SemilinearPointStabilizer.Coordinates
