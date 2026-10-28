module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.CycleData
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsHigh
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.Inverse

/-!
# Certifying the first J3 B row from 515 seed transitions

For each nontrivial B-cycle, two certified transitions determine the third:
B³ = 1 and the three factors multiply to one. The latter identity is proved
inside H1 using its two-point base, conditional only on the independent second
stabilizer step. The finite coverage theorem supplies either an algebraic
transition, a seed, or a cycle whose other two transitions are already known.
The lower and upper seed certificates complete the row, with only the
independent second stabilizer equality as a premise.
Source: `Order/data/witnesses.json`, ATLAS J3G1-p6156B0.
-/

namespace Sporadic.Janko3.OrderCertificate.Level0
open Theory.GroupTheory

namespace ForwardB

/-- The remaining full-permutation identities after word and cycle reduction. -/
public abbrev SeedSteps : Prop := ∀ r, Seed r →
  L0Gen 1 * L0Rep r = L0Rep (L0Act 1 r) * evalWord L1Gen (L0Factor 1 r)

private theorem cycle_cancel
    (hstab : H2 = H1 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 6156)) (1 : Fin 6156))
    (r : Fin 6156) (hr : Omitted r) :
    evalWord L1Gen (L0Factor 1 (L0Act 1 (L0Act 1 r))) *
      evalWord L1Gen (L0Factor 1 (L0Act 1 r)) * evalWord L1Gen (L0Factor 1 r) = 1 := by
  let g : H1 := ⟨evalWord L1Gen (L0Factor 1 (L0Act 1 (L0Act 1 r))) *
    evalWord L1Gen (L0Factor 1 (L0Act 1 r)) * evalWord L1Gen (L0Factor 1 r), H1.mul_mem
    (H1.mul_mem (evalWord_mem_wordSubgroup L1Gen L1Inv L1Inv_spec _)
      (evalWord_mem_wordSubgroup L1Gen L1Inv L1Inv_spec _))
    (evalWord_mem_wordSubgroup L1Gen L1Inv L1Inv_spec _)⟩
  exact congrArg (fun k : H1 => (k : Equiv.Perm (Fin 6156)))
    (H1_base_trivial hstab g (cycle_fix r hr 0) (cycle_fix r hr 1))

private theorem third_of_cycle {G : Type*} [Group G]
    (a x y z f g h : G) (ha : a * a * a = 1)
    (h1 : a * y = z * g) (h2 : a * z = x * h) (hf : h * g * f = 1) :
    a * x = y * f := by
  symm
  calc
    y * f = (a * (a * (a * y))) * f := by
      simp only [← mul_assoc, ha, one_mul]
    _ = (a * x) * (h * g * f) := by
      rw [h1, ← mul_assoc a z g, h2]
      simp only [mul_assoc]
    _ = a * x := by rw [hf, mul_one]

end ForwardB

/-- Assemble the B row from its seed checks and the independent H1 stabilizer theorem. -/
public theorem forwardRow1_of_seedSteps
    (hstab : H2 = H1 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 6156)) (1 : Fin 6156))
    (hseed : ForwardB.SeedSteps) : ForwardRow 1 := by
  have hk (r : Fin 6156) (hr : ForwardB.Known r) :
      L0Gen 1 * L0Rep r = L0Rep (L0Act 1 r) * evalWord L1Gen (L0Factor 1 r) := by
    rcases hr with hr | hr
    · exact algebraic_step 1 r hr
    · exact hseed r hr
  intro r
  rcases ForwardB.coverage r with hr | ⟨hr, hs, ht⟩
  · exact hk r hr
  · apply ForwardB.third_of_cycle (L0Gen 1) (L0Rep r)
      (L0Rep (L0Act 1 r)) (L0Rep (L0Act 1 (L0Act 1 r)))
      (evalWord L1Gen (L0Factor 1 r))
      (evalWord L1Gen (L0Factor 1 (L0Act 1 r)))
      (evalWord L1Gen (L0Factor 1 (L0Act 1 (L0Act 1 r))))
    · change atlasB * atlasB * atlasB = 1
      simpa only [pow_succ, pow_zero, one_mul] using atlasB_cube
    · exact hk _ hs
    · simpa only [ForwardB.act_cube] using hk _ ht
    · exact ForwardB.cycle_cancel hstab r hr

/-- The first B Schreier row, using the independent second stabilizer step. -/
public theorem forwardRow1
    (hstab : H2 = H1 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 6156)) (1 : Fin 6156)) :
    ForwardRow 1 := by
  apply forwardRow1_of_seedSteps hstab
  intro r hr
  rcases lt_or_ge r.val 4714 with hlt | hge
  · exact ForwardB.seedStepsLow r hr hlt
  · exact ForwardB.seedStepsHigh r hr hge

end Sporadic.Janko3.OrderCertificate.Level0
