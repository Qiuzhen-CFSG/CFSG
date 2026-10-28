module
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# Perfect central covers of the binary three-dimensional linear group

The order 168 makes every odd Sylow subgroup cyclic. Transfer therefore
kills the odd part of the kernel of a perfect central cover; trivial two-core
kills its remaining two-part. The resulting equivalence retains the literal
projection, as required by the small-component source in15.3.31.

Source: Aschbacher–Smith C.1.31 and15.3.31, printed pp.135,1132;
the cyclic-Sylow transfer theorem is I.1.2, printed p.407.
-/
public noncomputable section
open Subgroup
namespace Matrix.PSL3Two
private theorem square_not_dvd_card {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    ¬ p ^ 2 ∣ Nat.card SL := by
  rw [card_SL]
  intro hs
  have hd : p ∣ 2^3 * 3 * 7 := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hs
  rcases hp.dvd_mul.mp hd with hd | hd
  · rcases hp.dvd_mul.mp hd with hd | hd
    · exact h2 ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow hd) |>.resolve_left hp.ne_one)
    · have he : p = 3 := (Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left hp.ne_one
      subst p
      norm_num at hs
  · have he : p = 7 := (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd |>.resolve_left hp.ne_one
    subst p
    norm_num at hs

/-- Every odd Sylow subgroup in the binary three-dimensional special linear
carrier is cyclic, including primes absent from its order. -/
theorem odd_sylow_isCyclic {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2)
    (P : Sylow p SL) : IsCyclic P := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨n,hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hn1 : n ≤ 1 := by
    by_contra h
    exact square_not_dvd_card hp h2
      ((pow_dvd_pow p (by omega : 2 ≤ n)).trans (hn ▸ P.card_subgroup_dvd_card))
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [hn]
  simpa using pow_dvd_pow p hn1

/-- A perfect central cover of SL₃(2) with trivial two-core has its literal
projection as an isomorphism; cyclic odd Sylow transfer removes the kernel. -/
def centralCoverEquiv {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E SL) (hc : pCore 2 E = ⊥) : E ≃* SL :=
  f.equivOfPCoreEqBotOfCyclicSylow hc (fun _ hp h2 => odd_sylow_isCyclic hp h2)

theorem centralCoverEquiv_apply {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E SL) (hc : pCore 2 E = ⊥) (x : E) :
    centralCoverEquiv f hc x = f.toMonoidHom x := by
  unfold centralCoverEquiv
  exact f.equivOfPCoreEqBotOfCyclicSylow_apply hc _ x
end Matrix.PSL3Two
