module

public import Theory.GroupTheory.SelfCentralizingCoreInheritance

/-!
# Centralizers of the displacement layer in characteristic p

If O_p(G) contains its centralizer and [O_p(G),G] lies in a normal subgroup
N, then C_G(N) lies in O_p(G). An element of prime order different from p
in C_G(N) acts quadratically on O_p(G). Coprime commutator idempotence makes
its action trivial, and self-centralization excludes that element. Cauchy's
theorem makes the whole normal centralizer a p-group.

Source application: Aschbacher–Smith E.2.13(7), printed p.225, after taking
the genuine central quotient by V∩V^g.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem centralizer_le_pCore_of_core_commutator
    (N : Subgroup G) [N.Normal]
    (hc : centralizer (pCore p G : Set G) ≤ pCore p G)
    (hcomm : ⁅pCore p G, (⊤ : Subgroup G)⁆ ≤ N) :
    centralizer (N : Set G) ≤ pCore p G := by
  let C := centralizer (N : Set G)
  have hCp : IsPGroup p C := by
    apply (isPGroup_iff_primeFactors_card_subset (Fact.out : p.Prime).ne_zero).mpr
    intro r hr
    obtain ⟨hrprime, hrdvd, _⟩ := Nat.mem_primeFactors.mp hr
    by_cases he : r = p
    · subst r
      exact Nat.mem_primeFactors.mpr ⟨Fact.out, dvd_rfl, (Fact.out : p.Prime).ne_zero⟩
    · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := C) r (hp := ⟨hrprime⟩) hrdvd
      let Q := pCore p G
      let R := zpowers (x : G)
      have hRC : R ≤ C := zpowers_le.mpr x.property
      have hQR : ⁅Q, R⁆ ≤ N := (commutator_mono le_rfl le_top).trans hcomm
      have hquad : ⁅⁅Q, R⁆, R⁆ = ⊥ :=
        commutator_eq_bot_iff_le_centralizer.mpr
          (hQR.trans (le_centralizer_iff.mp hRC))
      have hRcard : Nat.card R = r := by
        rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
      have hcop : Nat.Coprime (Nat.card R) (Nat.card Q) := by
        obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := G)).exists_card_eq
        rw [hRcard, hn]
        exact ((hrprime.coprime_iff_not_dvd).mpr
          (fun hd => he ((Nat.dvd_prime Fact.out).mp hd |>.resolve_left hrprime.ne_one))).pow_right n
      let : Group.IsNilpotent Q := (pCore_isPGroup (p := p) (G := G)).isNilpotent
      have hbot := commutator_eq_bot_of_coprime_quadratic Q R
        le_normalizer_of_normal (inferInstance : Group.IsSolvable Q) hcop hquad
      have hxQ : (x : G) ∈ Q := hc
        ((commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm] : ⁅R, Q⁆ = ⊥))
          (mem_zpowers _))
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := G)).exists_orderOf_dvd_pow ⟨x, hxQ⟩
      have hd : r ∣ p ^ n := by
        simpa only [Subgroup.orderOf_mk, Subgroup.orderOf_coe x, hx] using hn
      exact (he ((Nat.dvd_prime Fact.out).mp (hrprime.dvd_of_dvd_pow hd) |>.resolve_left hrprime.ne_one)).elim
  exact le_sSup ⟨inferInstance, hCp⟩
end Subgroup
