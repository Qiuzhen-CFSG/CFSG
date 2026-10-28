module

public import Theory.GroupTheory.CoveringPGroupDescent

/-!
# Comparison kernels from multiplier divisibility bounds

For surjections U → H → S, the kernel order of U → S is the product of
the two intervening kernel orders. Consequently a bound dividing
`p^r * |ker(H → S)|` makes `ker(U → H)` a p-group. If U → S is universal,
the existing p-core descent then maps H onto every covering L → S with
trivial p-core. The commuting projection triangle is preserved.

This supplies the order-only form of the canonical/exceptional separation
in GLS3, Theorem 6.1.4 and Corollary 6.1.5, without computing a multiplier's
full group structure. Its concrete unitary application is in Chapter B's
`EvenCoverLifting.UnitaryHigher`.
-/

public section

open Subgroup
namespace Theory.GroupTheory

private theorem card_eq_kernel_mul_target
    {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f) :
    Nat.card G = Nat.card f.ker * Nat.card H := by
  have h := f.ker.card_mul_index
  rw [Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at h
  exact h.symm

/-- The kernel orders multiply in a surjective commuting triangle. -/
theorem kernel_card_eq_mul_of_surjective_factor
    {U H S : Type*} [Group U] [Group H] [Group S] [Finite U] [Finite H] [Finite S]
    (c : U →* S) (f : H →* S) (a : U →* H)
    (hf : Function.Surjective f) (ha : Function.Surjective a)
    (hfac : f.comp a = c) :
    Nat.card c.ker = Nat.card a.ker * Nat.card f.ker := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := S))
  calc
    Nat.card c.ker * Nat.card S = Nat.card U :=
      (card_eq_kernel_mul_target c (hfac ▸ hf.comp ha)).symm
    _ = Nat.card a.ker * Nat.card H := card_eq_kernel_mul_target a ha
    _ = (Nat.card a.ker * Nat.card f.ker) * Nat.card S := by
      rw [card_eq_kernel_mul_target f hf, Nat.mul_assoc]

namespace Covering
universe u v w z
variable {S : Type u} {U : Type v} {L : Type w} {H : Type z}
  [Group S] [Finite S] [IsQuasisimple S]
  [Group U] [Finite U] [IsQuasisimple U]
  [Group L] [Finite L] [IsQuasisimple L]
  [Group H] [Finite H] [IsQuasisimple H]

/-- Dividing the upper kernel bound by the actual lower kernel order leaves
only a prime power in the comparison kernel. No exact multiplier is needed. -/
theorem comparison_kernel_isPGroup_of_card_dvd {p r : ℕ} [Fact p.Prime]
    (c : Covering U S) (a : Covering U H) (f : Covering H S) (hfac : f.comp a = c)
    (hcard : Nat.card c.toMonoidHom.ker ∣ p ^ r * Nat.card f.toMonoidHom.ker) :
    IsPGroup p a.toMonoidHom.ker := by
  have he := kernel_card_eq_mul_of_surjective_factor
    c.toMonoidHom f.toMonoidHom a.toMonoidHom f.surjective a.surjective
    (congrArg Covering.toMonoidHom hfac)
  rw [he] at hcard
  exact IsPGroup.of_card_dvd_pow
    ((Nat.mul_dvd_mul_iff_right (Nat.card_pos (α := f.toMonoidHom.ker))).mp hcard)

/-- A multiplier divisibility bound suffices for descent to a target with
trivial p-core, retaining the specified maps to the common base. -/
theorem IsUniversal.exists_covering_of_kernel_card_dvd {p r : ℕ} [Fact p.Prime]
    {c : Covering U S} (hc : IsUniversal.{u,v,w} c)
    (a : Covering U H) (f : Covering H S) (hfac : f.comp a = c)
    (hcard : Nat.card c.toMonoidHom.ker ∣ p ^ r * Nat.card f.toMonoidHom.ker)
    (g : Covering L S) (hcore : pCore p L = ⊥) :
    ∃ k : Covering H L, g.comp k = f :=
  hc.exists_covering_of_pGroup_kernel a f hfac
    (comparison_kernel_isPGroup_of_card_dvd c a f hfac hcard) g hcore

end Covering
end Theory.GroupTheory
