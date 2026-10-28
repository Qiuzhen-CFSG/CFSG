module

public import Theory.GroupTheory.QuasithinBasic
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Logic.Equiv.Option

/-!
# Independent cyclic actions in an actual two-local subgroup

Three commuting elements, each acting with order p on one of three
nontrivial two-subgroups and centralizing the other two, generate an abelian
group surjecting onto three cyclic groups of order p. Its Sylow p-subgroup
still surjects, so its generator rank is at least three. All three elements
normalize the join of the two-subgroups, giving the required actual two-local.

Transitivity on the nonidentity elements of a two-group of order greater
than two supplies the odd-prime action used here, by orbit--stabilizer and
Cauchy's theorem on the actual conjugation image. The action's centralizer
kernel need not split. The source application is in Bender.ThreeComponentRank.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
Proposition 2.2.2, printed p.520 (PDF p.537).
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Commuting cyclic lifts of three independent prime-order actions force
rank three inside the literal normalizer of the join of the acted-on groups. -/
theorem three_cyclic_actions_local_rank
    (U : Subgroup G) (Q : Fin 3 → Subgroup G) (b : Fin 3 → G)
    (hU : IsPGroup 2 U) (hQU : ∀ i, Q i ≤ U) (hQne : Q 0 ≠ ⊥)
    (hn : ∀ i j, b i ∈ normalizer (Q j : Set G))
    (hc : ∀ i j, Commute (b i) (b j))
    (hoff : ∀ i j, i ≠ j → b j ∈ centralizer (Q i : Set G))
    (p : ℕ) [Fact p.Prime]
    (ho : ∀ i, orderOf ((Q i).normalizerMonoidHom ⟨b i, hn i i⟩) = p) :
    ∃ H : Subgroup G, IsTwoLocal H ∧ 3 ≤ primeRank p H := by
  classical
  let A : Subgroup G := closure (Set.range b)
  have hb (i : Fin 3) : b i ∈ A := subset_closure ⟨i, rfl⟩
  let ba (i : Fin 3) : A := ⟨b i, hb i⟩
  let _ : IsMulCommutative A := isMulCommutative_closure (by
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    exact hc i j)
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  have hAn (i : Fin 3) : A ≤ normalizer (Q i : Set G) :=
    (closure_le (K := normalizer (Q i : Set G))).mpr
      (by rintro x ⟨j, rfl⟩; exact hn j i)
  let g (i : Fin 3) : A →* MulAut (Q i) := (Q i).normalizerMonoidHom.comp (inclusion (hAn i))
  have goff (i j : Fin 3) (hij : i ≠ j) : g i (ba j) = 1 := by
    ext q
    change b j * (q : G) * (b j)⁻¹ = (q : G)
    rw [← hoff i j hij q q.property, mul_inv_cancel_right]
  let R (i : Fin 3) : Subgroup (MulAut (Q i)) := zpowers (g i (ba i))
  let (i : Fin 3) : CommGroup (R i) := IsMulCommutative.instCommGroup
  have hgR (i : Fin 3) (a : A) : g i a ∈ R i := by
    obtain ⟨a, ha⟩ := a
    induction ha using closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      by_cases he : i = j
      · subst j
        exact mem_zpowers _
      · rw [show g i ⟨b j, _⟩ = 1 from goff i j he]
        exact one_mem _
    | one => exact (g i).map_one ▸ (one_mem (R i))
    | mul x y hx hy hix hiy =>
      change g i (⟨x, hx⟩ * ⟨y, hy⟩) ∈ R i
      rw [map_mul]
      exact mul_mem hix hiy
    | inv x hx hix =>
      change g i (⟨x, hx⟩⁻¹) ∈ R i
      rw [map_inv]
      exact inv_mem hix
  let f (i : Fin 3) : A →* R i := (g i).codRestrict (R i) (hgR i)
  let F : A →* ∀ i : Fin 3, R i := MonoidHom.pi f
  have hF : Function.Surjective F := by
    intro y
    choose k hk using fun i => (mem_zpowers_iff.mp (y i).property)
    refine ⟨∏ j : Fin 3, ba j ^ k j, ?_⟩
    funext i
    change f i (∏ j : Fin 3, ba j ^ k j) = y i
    rw [map_prod]
    have he : (∏ j : Fin 3, f i (ba j ^ k j)) = f i (ba i ^ k i) := by
      apply Finset.prod_eq_single i
      · intro j _ hji
        apply Subtype.ext
        change g i (ba j ^ k j) = 1
        rw [map_zpow, goff i j (Ne.symm hji), one_zpow]
      · simp
    rw [he]
    apply Subtype.ext
    change g i (ba i ^ k i) = (y i : MulAut (Q i))
    rw [map_zpow]
    exact hk i
  have horder (i : Fin 3) : orderOf (g i (ba i)) = p := ho i
  let (i : Fin 3) : IsElementaryAbelian p (R i) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (horder i ▸ pow_orderOf_eq_one (g i (ba i)))
  have hpow (a : ∀ i : Fin 3, R i) : a ^ p = 1 := by
    funext i
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p (R i)) (a i)
  have htcard : Nat.card (∀ i : Fin 3, R i) = p ^ 3 := by
    simp only [Nat.card_pi, R, Nat.card_zpowers, horder, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hrt : 3 ≤ Group.rank (∀ i : Fin 3, R i) := by
    apply (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp
    rw [← htcard]
    exact card_dvd_exponent_pow_rank' _ hpow
  let P : Sylow p A := Sylow.nonempty.some
  have htp : IsPGroup p (∀ i : Fin 3, R i) := fun a => ⟨1, by simpa using hpow a⟩
  have hmap : (P : Subgroup A).map F = ⊤ :=
    ((P.mapSurjective hF).is_maximal' (htp.to_subgroup ⊤) le_top).symm
  have hsP : Function.Surjective (F.comp (P : Subgroup A).subtype) := by
    apply MonoidHom.range_eq_top.mp
    simpa only [MonoidHom.range_comp, range_subtype] using hmap
  have hrA : 3 ≤ primeRank p A := hrt.trans
    ((Group.rank_le_of_surjective _ hsP).trans
      ((P : Subgroup A).rank_le_primeRank p P.isPGroup'))
  let D : Subgroup G := Q 0 ⊔ (Q 1 ⊔ Q 2)
  have hDU : D ≤ U := sup_le (hQU 0) (sup_le (hQU 1) (hQU 2))
  have hDne : D ≠ ⊥ := by
    intro he
    exact hQne (le_bot_iff.mp (he ▸ (le_sup_left : Q 0 ≤ D)))
  have hAD : A ≤ normalizer (D : Set G) := by
    have h12 := (le_inf (hAn 1) (hAn 2)).trans
      (normalizer_inf_normalizer_le_normalizer_sup (Q 1) (Q 2))
    exact (le_inf (hAn 0) h12).trans
      (normalizer_inf_normalizer_le_normalizer_sup (Q 0) (Q 1 ⊔ Q 2))
  exact ⟨normalizer (D : Set G), ⟨D, hDne, hU.to_le hDU, rfl⟩,
    hrA.trans (primeRank_le_of_injective p (inclusion hAD) (inclusion_injective hAD))⟩

/-- Local transitivity supplies an odd-prime-order element in the actual
conjugation image, without splitting its full centralizer kernel. -/
theorem exists_odd_prime_conjugation_action
    (N Q : Subgroup G) (hNQ : N ≤ normalizer (Q : Set G))
    (hQ : IsPGroup 2 Q) (hsize : 2 < Nat.card Q)
    (htrans : ∀ a : Q, a ≠ 1 → ∀ b : Q, b ≠ 1 →
      ∃ n : N, (Q.normalizerMonoidHom.comp (inclusion hNQ)) n a = b) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ n : N,
      orderOf ((Q.normalizerMonoidHom.comp (inclusion hNQ)) n) = p := by
  classical
  let _ : Fintype Q := Fintype.ofFinite Q
  let f := (Q.normalizerMonoidHom.comp (inclusion hNQ))
  let K := f.range
  have hQne : Q ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hsize
    omega
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hQne
  have horbit : MulAction.orbit K a = {q : Q | q ≠ 1} := by
    ext q
    constructor
    · rintro ⟨k, rfl⟩ he
      exact ha ((k : MulAut Q).injective (he.trans (map_one (k : MulAut Q)).symm))
    · intro hq
      obtain ⟨n, hn⟩ := htrans a ha q hq
      exact ⟨⟨f n, ⟨n, rfl⟩⟩, hn⟩
  have hplus : Nat.card (MulAction.orbit K a) + 1 = Nat.card Q := by
    rw [horbit]
    change Nat.card {q : Q // q ≠ 1} + 1 = Nat.card Q
    calc
      Nat.card {q : Q // q ≠ 1} + 1 = Nat.card (Option {q : Q // q ≠ 1}) := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_option]
      _ = Nat.card Q := Nat.card_congr (Equiv.optionSubtypeNe (1 : Q))
  obtain ⟨d, hd⟩ := hQ.exists_card_eq
  have hd0 : d ≠ 0 := by intro he; rw [he, pow_zero] at hd; omega
  have heven : Even (Nat.card Q) := hd ▸ (show Even 2 from by decide).pow_of_ne_zero hd0
  have ho : Odd (Nat.card (MulAction.orbit K a)) := by
    obtain ⟨m, hm⟩ := heven
    exact ⟨m - 1, by omega⟩
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
    (show Nat.card (MulAction.orbit K a) ≠ 1 by omega)
  have hop : Odd p := Nat.not_even_iff_odd.mp (by
    intro he
    exact ho.not_two_dvd_nat (he.two_dvd.trans hpd))
  have hdK : Nat.card (MulAction.orbit K a) ∣ Nat.card K := by
    refine ⟨Nat.card (MulAction.stabilizer K a), ?_⟩
    exact (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K a)).symm.trans
      (Nat.card_prod _ _)
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' p (hpd.trans hdK)
  obtain ⟨n, hn⟩ := k.property
  refine ⟨p, hp, hop, n, ?_⟩
  change orderOf (f n) = p
  rw [hn]
  exact (orderOf_injective K.subtype Subtype.val_injective k).trans hk


end Theory.GroupTheory
