module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.LinearGeometry
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The marked square-field consequence for Proposition 16.5

An arbitrary outer square-one automorphism preserving a Sylow normalizer
and fixing an outside involution acts on their two-point torus by the
square-root Frobenius. The same square-root exponent identifies its actual
fixed group. For a prime dividing r+1, the p-core of the torus has order
dividing r+1, since r−1 and r+1 have relatively prime odd parts. Thus that
literal ambient p-core is inverted by the automorphism.

Source: GLS IV, Chapter 4, Lemma 3.4(a,c), applied in Chapter 2,
Proposition 16.5 to R₀ = Oₚ(D ∩ B°).
-/

public section
namespace BenderSuzuki.ZD.RankOneModelGeometry
open Subgroup _root_.BenderSuzuki.MatrixGroups PFAppendixIII PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

private theorem sqrt_power_eq_inv_on_pCore (D : Subgroup G) {m p : ℕ}
    (hm : 0 < m) (hp : p.Prime) (hpdiv : p ∣ 2 ^ m + 1)
    (hD : Nat.card D = (2 ^ m - 1) * (2 ^ m + 1))
    {x : G} (hx : x ∈ D.pCoreIn p) : x ^ (2 ^ m) = x⁻¹ := by
  let : Fact p.Prime := ⟨hp⟩
  have hr : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
  have htwo : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    omega
  have hcop : Nat.Coprime p (2 ^ m - 1) := hp.coprime_iff_not_dvd.mpr (by
    intro hd
    have hd2 : p ∣ 2 := by
      have hh := Nat.dvd_sub hpdiv hd
      convert hh using 1
      omega
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hd2 |>.resolve_left hp.ne_one))
  obtain ⟨k, hk⟩ := (isPGroup_pCoreIn p D).exists_card_eq
  have hdiv : p ^ k ∣ (2 ^ m - 1) * (2 ^ m + 1) := by
    rw [← hk, ← hD]
    exact card_dvd_of_le (pCoreIn_le p D)
  have hq : Nat.card (D.pCoreIn p) ∣ 2 ^ m + 1 := by
    rw [hk]
    exact (hcop.pow_left k).dvd_of_dvd_mul_left hdiv
  have hpow : x ^ (2 ^ m + 1) = 1 := by
    have hh := pow_card_eq_one' (x := (⟨x, hx⟩ : D.pCoreIn p))
    have hh' : x ^ Nat.card (D.pCoreIn p) = 1 := congrArg Subtype.val hh
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one hh').trans hq)
  exact eq_inv_of_mul_eq_one_left (by simpa only [pow_succ] using hpow)

/-- The fixed group and marked torus action use the same square-root field;
in particular every literal ambient p-core for p dividing r+1 is inverted. -/
theorem linear_outer_marked_fixed_and_pCore {n : ℕ} (hn : 2 ≤ n)
    (e : G ≃* PSL2BinaryMatrixGroup n) (P : Sylow 2 G)
    (t : G) (ht : IsInvolution t) (htB : t ∉ normalizer (P : Set G))
    (a : MulAut G) (ha : a ^ 2 = 1) (houter : ¬ ∃ g : G, a = MulAut.conj g)
    (haB : (normalizer (P : Set G)).map a.toMonoidHom = normalizer (P : Set G))
    (hat : a t = t) :
    ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧
      Nonempty (a.fixedSubgroup ≃* PSL2BinaryMatrixGroup m) ∧
      (∀ x ∈ twoPoint (normalizer (P : Set G)) t, a x = x ^ (2 ^ m)) ∧
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ m + 1 →
        ∀ x ∈ (twoPoint (normalizer (P : Set G)) t).pCoreIn p, a x = x⁻¹ := by
  obtain ⟨m, hm, hnm, hpower⟩ :=
    LinearGeometry.outer_marked_torus_power (by omega) e P ht htB a ha houter haB hat
  have ha' : (MulAut.congr e a) ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  have ho' : ¬ ∃ g, MulAut.congr e a = MulAut.conj g := fun h =>
    houter ((MulAut.congr_inner_iff e a).mp h)
  obtain ⟨m', _, hnm', ⟨f⟩⟩ := Linear.outer_fixed_model hn (MulAut.congr e a) ha' ho'
  have heq : m' = m := by omega
  subst m'
  refine ⟨m, hm, hnm, ⟨(MulAut.fixedSubgroupCongr e a).trans f⟩, hpower, ?_⟩
  intro p hp hpdiv x hx
  rw [hpower x (pCoreIn_le p _ hx)]
  apply sqrt_power_eq_inv_on_pCore _ hm hp hpdiv _ hx
  have hcard : Nat.card (twoPoint (normalizer (P : Set G)) t) = 2 ^ n - 1 :=
    (LinearGeometry.twoPoint_cyclic_card (by omega) e P ht htB).2
  rw [hcard, hnm, mul_comm 2 m, pow_mul]
  have hr : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by decide)
  have hs : 2 ^ m - 1 + 1 = 2 ^ m := Nat.sub_add_cancel hr
  have hr2 : 1 ≤ (2 ^ m) ^ 2 := by nlinarith
  have hs2 := Nat.sub_add_cancel hr2
  nlinarith

end BenderSuzuki.ZD.RankOneModelGeometry
