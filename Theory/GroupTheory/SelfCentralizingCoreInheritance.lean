module
public import Theory.GroupTheory.Commutator.CoprimeQuadratic
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.Quasithin.EvenCharacteristic
public import Mathlib.GroupTheory.IsSubnormal

/-!
# Characteristic p passes to subnormal subgroups

Let `Q = O_p(G)` contain its centralizer. For a normal subgroup `N`, an
odd-to-p prime-order element in `C_N(Q ∩ N)` acts quadratically on `Q`:
its commutators lie in `Q ∩ N`, which it centralizes. Coprime commutator
idempotence makes this action trivial, so the element belongs to `Q`.
Cauchy's theorem therefore makes `C_N(Q ∩ N)` a p-group, proving that
`O_p(N)` contains its centralizer. Induction down a subnormal chain gives
the general result.

This is the inheritance used for the component intersection in
Aschbacher–Smith, Lemma 2.3.9(7)(c), printed pp.525–526, from the local
characteristic-two conclusion of 2.3.9(4). It uses intrinsic subgroup
cores and relative subnormality throughout.
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private theorem prime_order_centralizer_normal_core
    (N : Subgroup G) [N.Normal]
    (hc : centralizer (pCore p G : Set G) ≤ pCore p G)
    (x : N) (hx : x ∈ centralizer ((pCore p G).subgroupOf N : Set N))
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) (ho : orderOf x = q) : False := by
  let Q := pCore p G
  let R := zpowers (x : G)
  have hRQ : R ≤ normalizer (Q : Set G) := by
    rw [normalizer_eq_top_iff.mpr (inferInstance : Q.Normal)]
    exact le_top
  have hRN : R ≤ N := zpowers_le.mpr x.property
  have hQR : ⁅Q, R⁆ ≤ Q ⊓ N :=
    le_inf (commutator_le_left Q R)
      ((commutator_mono le_rfl hRN).trans (commutator_le_right Q N))
  have hcent : Q ⊓ N ≤ centralizer (R : Set G) := by
    change Q ⊓ N ≤ centralizer (zpowers (x : G) : Set G)
    rw [zpowers_eq_closure, centralizer_closure]
    intro y hy
    have he := congrArg Subtype.val (mem_centralizer_iff.mp hx ⟨y, hy.2⟩ hy.1)
    exact mem_centralizer_singleton_iff.mpr he
  have hquad : ⁅⁅Q, R⁆, R⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (hQR.trans hcent)
  have hRcard : Nat.card R = q := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ho]
  have hcop : Nat.Coprime (Nat.card R) (Nat.card Q) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := G)).exists_card_eq
    rw [hRcard, hn]
    exact ((hq.coprime_iff_not_dvd).mpr
      (fun hd => hqp ((Nat.dvd_prime Fact.out).mp hd |>.resolve_left hq.ne_one))).pow_right n
  let : Group.IsNilpotent Q := (pCore_isPGroup (p := p) (G := G)).isNilpotent
  have hbot := commutator_eq_bot_of_coprime_quadratic Q R hRQ
    (inferInstance : Group.IsSolvable Q) hcop hquad
  have hxQ : (x : G) ∈ Q := hc
    ((commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm] : ⁅R, Q⁆ = ⊥))
      (mem_zpowers _))
  have hpo := (pCore_isPGroup (p := p) (G := G)).exists_orderOf_dvd_pow ⟨x, hxQ⟩
  obtain ⟨n, hn⟩ := hpo
  have hd : q ∣ p ^ n := by
    simpa only [Subgroup.orderOf_mk, Subgroup.orderOf_coe x, ho] using hn
  exact hqp ((Nat.dvd_prime Fact.out).mp (hq.dvd_of_dvd_pow hd) |>.resolve_left hq.ne_one)

/-- Characteristic p is inherited by normal subgroups of a finite group. -/
public theorem normal_core_selfCentralizing
    (hc : centralizer (pCore p G : Set G) ≤ pCore p G)
    (N : Subgroup G) [N.Normal] :
    centralizer (pCore p N : Set N) ≤ pCore p N := by
  let C := centralizer ((pCore p G).subgroupOf N : Set N)
  have hCp : IsPGroup p C := by
    apply (isPGroup_iff_primeFactors_card_subset (Fact.out : p.Prime).ne_zero).mpr
    intro q hq
    obtain ⟨hqprime, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
    by_cases he : q = p
    · subst q
      exact Nat.mem_primeFactors.mpr ⟨Fact.out, dvd_rfl, (Fact.out : p.Prime).ne_zero⟩
    · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := C) q (hp := ⟨hqprime⟩) hqdvd
      exact (prime_order_centralizer_normal_core N hc x x.property hqprime he
        (by simpa only [Subgroup.orderOf_coe] using hx)).elim
  have hCcore : C ≤ pCore p N := le_sSup ⟨inferInstance, hCp⟩
  have hQN : (pCore p G).subgroupOf N ≤ pCore p N :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  exact (centralizer_le hQN).trans hCcore

/-- Characteristic p is inherited by subnormal subgroups of a finite group. -/
public theorem subnormal_core_selfCentralizing
    (hc : centralizer (pCore p G : Set G) ≤ pCore p G)
    (N : Subgroup G) (hN : N.IsSubnormal) :
    centralizer (pCore p N : Set N) ≤ pCore p N := by
  induction hN with
  | top =>
    exact (Theory.Quasithin.centralizer_pCore_le_iff p Subgroup.topEquiv).mpr hc
  | step N K hNK _ hn ih =>
    let := hn
    exact (Theory.Quasithin.centralizer_pCore_le_iff p
      (Subgroup.subgroupOfEquivOfLe hNK)).mp
        (normal_core_selfCentralizing ih (N.subgroupOf K))
end Subgroup
