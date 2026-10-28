module

public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.GroupTheory.CommutatorOrbitCard

/-!
# The order of an exponent-p group of prime rank two

A finite p-group of exponent p, prime rank two and nilpotence class at most two
has order at most p³. Choose an elementary abelian subgroup E of order p².
The rank bound prevents adjoining any further element centralizing E, so E is
self-centralizing and contains the center Z. If E is proper, Z is a nontrivial
proper subgroup of E and hence has order p. For x in E outside Z, the subgroup
Z⟨x⟩ is all of E, giving C_P(x) ≤ E. Since commutators are central, the conjugacy
orbit of x has size at most |Z|. Orbit-stabilizer gives the desired bound.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Lemma A.1.24, printed p.25. This is the order-bound
step after exponent p has been established; concrete model recognition is
separate.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement

variable {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]

private theorem centralizer_le_of_elementary_plane
    (hpow : ∀ x : P, x ^ p = 1) (hrank : primeRank p P ≤ 2)
    (E : Subgroup P) [IsElementaryAbelian p E] (hE : Nat.card E = p ^ 2) :
    centralizer (E : Set P) ≤ E := by
  intro x hx
  let : IsElementaryAbelian p (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hpow x)
  let : IsElementaryAbelian p (E ⊔ zpowers x : Subgroup P) :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr hx)
  have hc := (primeRank_le_iff_elementary_card_le P).mp hrank
    (E ⊔ zpowers x) inferInstance
  have he : E = E ⊔ zpowers x := eq_of_le_of_card_ge le_sup_left (hE ▸ hc)
  exact he ▸ (mem_sup_right (mem_zpowers x))

/-- An exponent-p p-group of prime rank two and class at most two has order
at most p³. The odd-prime hypothesis retains the source's domain; the bound
itself only uses the stated exponent and class assumptions. -/
public theorem IsPGroup.card_le_prime_cube_of_exponent_prime_rank_two (hP : IsPGroup p P) (_hpodd : p ≠ 2)
    (hexp : Monoid.exponent P = p) (hrank : primeRank p P = 2)
    (hclass : commutator P ≤ center P) : Nat.card P ≤ p ^ 3 := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpow : ∀ x : P, x ^ p = 1 := fun x => hexp ▸ Monoid.pow_exponent_eq_one x
  obtain ⟨E, hEe, hEc⟩ := exists_elementaryAbelian_card_primeRank (G := P) (p := p)
  let : IsElementaryAbelian p E := hEe
  have hE : Nat.card E = p ^ 2 := by simpa only [hrank] using hEc
  have hCE : centralizer (E : Set P) ≤ E := centralizer_le_of_elementary_plane hpow hrank.le E hE
  by_cases htop : E = ⊤
  · have hc : Nat.card P = p ^ 2 := by simpa only [htop, card_top] using hE
    rw [hc]
    exact pow_le_pow_right' hp.le (by decide : 2 ≤ 3)
  have hZE : center P ≤ E := (center_le_centralizer (E : Set P)).trans hCE
  have hnot : ¬ E ≤ center P := by
    intro h
    have hC : centralizer (E : Set P) = ⊤ := centralizer_eq_top_iff_subset.mpr h
    exact htop (top_unique (hC ▸ hCE))
  obtain ⟨x, hxE, hxZ⟩ : ∃ x : P, x ∈ E ∧ x ∉ center P := by
    exact Set.not_subset.mp hnot
  have hx1 : x ≠ 1 := fun h => hxZ (h ▸ (center P).one_mem)
  let : Nontrivial P := ⟨⟨x, 1, hx1⟩⟩
  have hZlt : Nat.card (center P) < p ^ 2 := by
    apply lt_of_le_of_ne ((card_le_of_le hZE).trans hE.le)
    intro he
    have hZeq : center P = E := eq_of_le_of_card_ge hZE (by rw [he, hE])
    exact hxZ (hZeq ▸ hxE)
  obtain ⟨k, hk, hZk⟩ := (hP.to_subgroup (center P)).nontrivial_iff_card.mp
    hP.center_nontrivial
  have hk2 : k < 2 := (Nat.pow_lt_pow_iff_right hp).mp (hZk ▸ hZlt)
  have hZ : Nat.card (center P) = p := by
    have hk1 : k = 1 := by omega
    simpa only [hk1, pow_one] using hZk
  let : IsElementaryAbelian p (center P) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun z => by
      apply Subtype.ext
      exact hpow z) }
  have hxord : orderOf x = p := orderOf_eq_prime (hpow x) hx1
  have hjoin := IsElementaryAbelian.fixed_join_card (n := 1) (center P) x hxord
    ((center P).disjoint_zpowers_of_prime_order_not_mem x hxord hxZ)
    (center_le_centralizer _) (by simpa only [pow_one] using hZ)
  have hgen : center P ⊔ zpowers x = E :=
    eq_of_le_of_card_ge (sup_le hZE (zpowers_le.mpr hxE)) (by rw [hE, hjoin.2])
  have hCx : centralizer ({x} : Set P) ≤ E := by
    intro y hy
    apply hCE
    have hEy : E ≤ centralizer ({y} : Set P) := by
      rw [← hgen]
      refine sup_le (center_le_centralizer _) (zpowers_le.mpr ?_)
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hy).symm
    exact mem_centralizer_iff.mpr (fun e he => mem_centralizer_singleton_iff.mp (hEy he))
  have hcomm : ⁅(⊤ : Subgroup P), zpowers x⁆ ≤ center P :=
    (commutator_mono le_rfl le_top).trans hclass
  have horbit := card_le_commutator_card_mul_centralizer (⊤ : Subgroup P) x
  have hcTop : Nat.card ((centralizer ({x} : Set P)).subgroupOf (⊤ : Subgroup P)) =
      Nat.card (centralizer ({x} : Set P)) :=
    Nat.card_congr (subgroupOfEquivOfLe le_top).toEquiv
  rw [card_top, hcTop] at horbit
  calc
    Nat.card P ≤ Nat.card (⁅(⊤ : Subgroup P), zpowers x⁆ : Subgroup P) *
        Nat.card (centralizer ({x} : Set P)) := horbit
    _ ≤ Nat.card (center P) * Nat.card E :=
      Nat.mul_le_mul (card_le_of_le hcomm) (card_le_of_le hCx)
    _ = p ^ 3 := by rw [hZ, hE]; ring
