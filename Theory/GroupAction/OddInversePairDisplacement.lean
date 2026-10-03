module

public import Theory.GroupAction.OddNormDisplacement
public import Theory.Comparator.Defs

/-!
# Inverse-pair factorization of odd norm displacement

An element inverting an odd-order subgroup pairs the subgroup's inverse
elements on every fixed vector. Modulo the inverter-displacement range,
these pairs cancel. If the actor-fixed subgroup is trivial, the odd norm
displacement is the identity, so every inverter-fixed vector is a displacement.

No cyclicity, faithfulness, solvability, or finiteness of the module is required.
-/

open scoped IsMulCommutative

namespace OddInversePairDisplacement

/-- An inverse-paired product over an odd group lies in the given subgroup. -/
public theorem prod_mem_of_inverse_pairs
    {A W : Type*} [Group A] [Fintype A] [CommGroup W]
    (hodd : Odd (Nat.card A)) (target : Subgroup W) (factor : A → W)
    (hone : factor 1 = 1)
    (hpair : ∀ actor, factor actor * factor actor⁻¹ ∈ target) :
    (∏ actor : A, factor actor) ∈ target := by
  let quotient := QuotientGroup.mk' target
  apply (QuotientGroup.eq_one_iff _).mp
  change quotient (∏ actor : A, factor actor) = 1
  rw [map_prod]
  apply Finset.prod_ninvolution Inv.inv
  · intro actor
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (hpair actor)
  · intro actor hne heq
    have hsquare : actor ^ 2 = 1 := by
      calc
        actor ^ 2 = actor⁻¹ * actor := by rw [pow_two, heq]
        _ = 1 := inv_mul_cancel actor
    have hactor : actor = 1 := by
      obtain ⟨count, hcount⟩ := hodd
      have hpower := pow_card_eq_one' (x := actor)
      simpa only [hcount, pow_add, pow_mul, hsquare, one_pow, pow_one, one_mul]
        using hpower
    exact hne (by simp [hactor, hone])
  · intro actor
    exact Finset.mem_univ _
  · exact inv_inv

variable {G V : Type*} [Group G] [Group V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]

private theorem elementary_inv_eq_self (value : V) : value⁻¹ = value := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [pow_two] using
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) value

/-- Displacement by a single actor on an elementary abelian two-group. -/
@[expose] public noncomputable def displacement (inverter : G) : V →* V where
  toFun vector := vector⁻¹ * (inverter • vector)
  map_one' := by simp
  map_mul' := by
    intro left right
    simp only [mul_inv_rev, smul_mul']
    ac_rfl

/-- Each inverse pair of relative displacements is an inverter displacement. -/
public theorem inverse_pair_eq_displacement
    (actors : Subgroup G) (inverter : G)
    (hinv : ∀ actor : actors,
      inverter * (actor : G) * inverter⁻¹ = (actor : G)⁻¹)
    (vector : V) (hvector : inverter • vector = vector) (actor : actors) :
    (vector⁻¹ * (actor • vector)) * (vector⁻¹ * (actor⁻¹ • vector)) =
      displacement inverter (actor • vector) := by
  have hcommute : inverter * (actor : G) = (actor : G)⁻¹ * inverter := by
    have hmul := congrArg (fun value : G => value * inverter) (hinv actor)
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmul
  have haction : inverter • (actor • vector) = actor⁻¹ • vector := by
    change inverter • ((actor : G) • vector) = ((actor : G)⁻¹) • vector
    rw [← mul_smul, hcommute, mul_smul, hvector]
  change _ = (actor • vector)⁻¹ * (inverter • (actor • vector))
  rw [haction, elementary_inv_eq_self (actor • vector)]
  calc
    _ = (vector⁻¹ * vector⁻¹) * ((actor • vector) * (actor⁻¹ • vector)) := by
      ac_rfl
    _ = _ := by
      have hcancel : vector⁻¹ * vector⁻¹ = 1 := by
        simpa only [elementary_inv_eq_self vector] using inv_mul_cancel vector
      rw [hcancel, one_mul]

/-- The odd norm displacement of an inverter-fixed vector factors through its displacement. -/
public theorem norm_displacement_mem_range
    (actors : Subgroup G) [Finite actors] (hodd : Odd (Nat.card actors))
    (inverter : G)
    (hinv : ∀ actor : actors,
      inverter * (actor : G) * inverter⁻¹ = (actor : G)⁻¹)
    (vector : V) (hvector : inverter • vector = vector) :
    OddNormDisplacement.displacement actors V vector ∈ (displacement inverter).range := by
  classical
  let _ := Fintype.ofFinite actors
  change (∏ actor : actors, vector⁻¹ * (actor • vector)) ∈ _
  apply prod_mem_of_inverse_pairs hodd
  · simp
  · intro actor
    rw [inverse_pair_eq_displacement actors inverter hinv vector hvector actor]
    exact ⟨actor • vector, rfl⟩

/-- Trivial actor-fixed subgroup makes every inverter-fixed vector a displacement. -/
public theorem fixed_mem_range
    (actors : Subgroup G) [Finite actors] (hodd : Odd (Nat.card actors))
    (inverter : G)
    (hinv : ∀ actor : actors,
      inverter * (actor : G) * inverter⁻¹ = (actor : G)⁻¹)
    (hfixed : FixedPoints.subgroup actors V = ⊥)
    (vector : V) (hvector : inverter • vector = vector) :
    vector ∈ (displacement inverter).range := by
  rw [← OddNormDisplacement.displacement_eq_self actors V hodd hfixed vector]
  exact norm_displacement_mem_range actors hodd inverter hinv vector hvector

/-- For an involution inverting a fixed-point-free odd actor, fixed vectors are exactly
displacements. -/
public theorem fixed_iff_exists_displacement
    (actors : Subgroup G) [Finite actors] (hodd : Odd (Nat.card actors))
    (inverter : G) (hinvolution : IsInvolution inverter)
    (hinv : ∀ actor : actors,
      inverter * (actor : G) * inverter⁻¹ = (actor : G)⁻¹)
    (hfixed : FixedPoints.subgroup actors V = ⊥) (vector : V) :
    inverter • vector = vector ↔
      ∃ preimage : V, preimage⁻¹ * (inverter • preimage) = vector := by
  constructor
  · exact fixed_mem_range actors hodd inverter hinv hfixed vector
  · rintro ⟨preimage, rfl⟩
    have htwice : inverter • (inverter • preimage) = preimage := by
      rw [← mul_smul, ← pow_two, hinvolution.2, one_smul]
    rw [smul_mul', smul_inv', htwice]
    simp only [elementary_inv_eq_self]
    exact mul_comm _ _

end OddInversePairDisplacement
