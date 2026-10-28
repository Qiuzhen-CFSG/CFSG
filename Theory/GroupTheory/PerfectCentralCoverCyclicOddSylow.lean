module

public import Theory.GroupTheory.PerfectCentralCover
public import Theory.PGroupCore

/-!
# Perfect central covers of groups with cyclic odd Sylow subgroups

If the p-core is trivial, no central subgroup has order divisible by p:
a central element of order p would generate a normal p-subgroup. For a
finite perfect central cover, cyclic Sylow subgroups in the target exclude
the corresponding primes from the kernel by transfer. Thus a perfect cover
of a group with cyclic odd Sylow subgroups is an isomorphism when its source
has trivial two-core.

This supplies the covering-group step for the Suzuki branch of
Aschbacher–Smith, B.1.13, printed p.73. The transfer input is I.1.2,
printed p.407; neither an FF-module nor a universal-cover computation is
needed for this particular family.
-/

public section

open Subgroup

namespace PerfectCentralCovering

/-- Trivial p-core excludes p from the order of every central subgroup. -/
theorem not_dvd_card_central_of_pCore_eq_bot
    {L : Type*} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]
    (hc : pCore p L = ⊥) (Z : Subgroup L) (hZ : Z ≤ center L) :
    ¬ p ∣ Nat.card Z := by
  intro hp
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hp
  let C := zpowers (z : L)
  have hC : C ≤ center L := zpowers_le.mpr (hZ z.property)
  have hnormal : C.Normal := ⟨fun n hn g => by
    have hcomm := mem_center_iff.mp (hC hn) g
    simpa only [hcomm, mul_assoc, mul_inv_cancel, mul_one] using hn⟩
  have hord : orderOf (z : L) = p := (Subgroup.orderOf_coe z).trans hz
  have hCp : IsPGroup p C := IsPGroup.of_card (n := 1) (by
    simpa only [C, Nat.card_zpowers, pow_one] using hord)
  have hle : C ≤ pCore p L := le_sSup ⟨hnormal, hCp⟩
  have hone : (z : L) = 1 := mem_bot.mp (hc ▸ hle (mem_zpowers _))
  exact (Fact.out : p.Prime).ne_one (hord.symm.trans (orderOf_eq_one_iff.mpr hone))

/-- Cyclic Sylow subgroups away from p make a perfect central cover with
trivial p-core injective. All primes, including primes absent from the target's
order, are covered by the transfer argument. -/
theorem Cover.injective_of_pCore_eq_bot_of_cyclic_sylow
    {L G : Type*} [Group L] [Finite L] [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (f : Cover L G) (hc : pCore p L = ⊥)
    (hcyclic : ∀ q : ℕ, q.Prime → q ≠ p → ∀ Q : Sylow q G, IsCyclic Q) :
    Function.Injective f.toMonoidHom := by
  apply (MonoidHom.ker_eq_bot_iff f.toMonoidHom).mp
  apply Subgroup.card_eq_one.mp
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro q hq
  let : Fact q.Prime := ⟨hq⟩
  by_cases he : q = p
  · subst q
    exact not_dvd_card_central_of_pCore_eq_bot hc f.toMonoidHom.ker f.ker_le_center
  · exact f.not_dvd_card_multiplier_of_isCyclic_sylow (hcyclic q hq he)

/-- The actual projection of the cover is the resulting isomorphism. -/
noncomputable def Cover.equivOfPCoreEqBotOfCyclicSylow
    {L G : Type*} [Group L] [Finite L] [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (f : Cover L G) (hc : pCore p L = ⊥)
    (hcyclic : ∀ q : ℕ, q.Prime → q ≠ p → ∀ Q : Sylow q G, IsCyclic Q) :
    L ≃* G :=
  MulEquiv.ofBijective f.toMonoidHom
    ⟨f.injective_of_pCore_eq_bot_of_cyclic_sylow hc hcyclic, f.surjective⟩

@[simp] theorem Cover.equivOfPCoreEqBotOfCyclicSylow_apply
    {L G : Type*} [Group L] [Finite L] [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (f : Cover L G) (hc : pCore p L = ⊥)
    (hcyclic : ∀ q : ℕ, q.Prime → q ≠ p → ∀ Q : Sylow q G, IsCyclic Q)
    (x : L) : f.equivOfPCoreEqBotOfCyclicSylow hc hcyclic x = f.toMonoidHom x := by
  unfold Cover.equivOfPCoreEqBotOfCyclicSylow
  rfl

end PerfectCentralCovering
