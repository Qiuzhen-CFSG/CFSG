module

public import Theory.SpecificGroups.Janko3.Model.Order.Level1.Batches

/-!
# Algebraic assembly of the second J3 stabilizer step

Transition identities decompose every word as a transversal representative
times an element of the terminal subgroup. Distinct base images identify the
point stabilizer, and the word-subgroup bijection gives the cardinality step.
The expensive concrete transition checks live separately from this argument.
Source: ATLAS J3G1-p6156B0, retained under `Model/data/`.
-/

namespace Sporadic.Janko3.OrderCertificate.Level1
open Theory.GroupTheory

/-- The Schreier identities give a decomposition of every level-1 element. -/
public theorem decomposition_of_step
    (hstep : ∀ (i : Fin 4) (r : Fin 510),
      L1Gen i * L1Rep r = L1Rep (L1Act i r) * evalWord L2Gen (L1Factor i r))
    (g : H1) : ∃ (r : Fin 510) (k : H2),
      (g : Equiv.Perm (Fin 6156)) = L1Rep r * (k : Equiv.Perm (Fin 6156)) := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ (r : Fin 510) (k : H2),
      evalWord L1Gen w = L1Rep r * (k : Equiv.Perm (Fin 6156)) by
    simpa only [hw] using this
  clear hw
  induction w with
  | nil =>
    exact ⟨0, 1, by simp only [evalWord, L1Rep_base, OneMemClass.coe_one, mul_one]⟩
  | cons i w ih =>
    obtain ⟨r, k, hk⟩ := ih
    refine ⟨L1Act i r,
      ⟨evalWord L2Gen (L1Factor i r) * (k : Equiv.Perm (Fin 6156)),
        H2.mul_mem (evalWord_mem_wordSubgroup L2Gen L2Inv L2Inv_spec _) k.property⟩, ?_⟩
    change L1Gen i * evalWord L1Gen w =
      L1Rep (L1Act i r) * (evalWord L2Gen (L1Factor i r) * (k : Equiv.Perm (Fin 6156)))
    rw [hk, ← mul_assoc, hstep, mul_assoc]

public theorem card_step_of_step
    (hstep : ∀ (i : Fin 4) (r : Fin 510),
      L1Gen i * L1Rep r = L1Rep (L1Act i r) * evalWord L2Gen (L1Factor i r)) :
    Nat.card H1 = 510 * Nat.card H2 := by
  exact wordSubgroup_card_eq_mul_next
    L1Gen L1Inv L1Inv_spec L2Gen L2Inv L2Inv_spec
    L1Rep L1Act L1Factor (1 : Fin 6156) L1Point (0 : Fin 510)
    L1Rep_mem H2_le L1Rep_base L1Rep_point L1Point_injective H2_fix hstep

public theorem stabilizer_of_step
    (hstep : ∀ (i : Fin 4) (r : Fin 510),
      L1Gen i * L1Rep r = L1Rep (L1Act i r) * evalWord L2Gen (L1Factor i r)) :
    H2 = H1 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 6156)) (1 : Fin 6156) := by
  apply le_antisymm
  · intro g hg
    exact ⟨H2_le hg, MulAction.mem_stabilizer_iff.mpr (H2_fix ⟨g, hg⟩)⟩
  · intro g hg
    obtain ⟨r, k, hgk⟩ := decomposition_of_step hstep ⟨g, hg.1⟩
    have hfix : g 1 = 1 := MulAction.mem_stabilizer_iff.mp hg.2
    have hp : L1Point r = L1Point 0 := by
      calc
        L1Point r = L1Rep r 1 := (L1Rep_point r).symm
        _ = (L1Rep r * (k : Equiv.Perm (Fin 6156))) 1 := by
          simp only [Equiv.Perm.mul_apply, H2_fix]
        _ = g 1 := congrArg (fun p : Equiv.Perm (Fin 6156) => p 1) hgk.symm
        _ = L1Point 0 := hfix
    have hr := L1Point_injective hp
    rw [hr, L1Rep_base, one_mul] at hgk
    change g = (k : Equiv.Perm (Fin 6156)) at hgk
    exact hgk.symm ▸ k.property

end Sporadic.Janko3.OrderCertificate.Level1
