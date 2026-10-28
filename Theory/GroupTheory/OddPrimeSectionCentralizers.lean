module

public import Theory.GroupTheory.OddPrimeSectionCentralizers.PrimeKernel

/-!
# Cyclic centralizers in sections of odd prime rank at most two

Induct on the order of the source of the surjection. If its kernel is not
a p-group, choose a Sylow r-subgroup of the kernel with r different from p.
The Frattini argument makes its normalizer surject onto the target. A proper
normalizer reduces the source order. Otherwise the Sylow subgroup is normal
in the source, and quotienting by it reduces the order while preserving
the needed prime-rank bound through its coprime kernel. The remaining
p-group-kernel case is proved in PrimeKernel.

The rank hypothesis stays on the source throughout. No rank monotonicity
for arbitrary quotients, solvability, or splitting assumption is used.
The final equivalence identifies the internal centralizer with the ambient
intersection on the actual subgroup carriers.

Source: Aschbacher–Smith, Lemma A.1.31(1), printed pp.27–28
(1 March 2004 combined manuscript).
-/

public section

open Subgroup
namespace Theory.GroupTheory
universe u v

/-- A nontrivial two-subgroup of a characteristic-p image has cyclic centralizer
in the prime core, provided the source has odd prime rank at most two. -/
theorem cyclic_primeCore_centralizer_of_surjective_rank_le_two
    {A : Type u} [Group A] [Finite A] {D : Type v} [Group D] [Finite D]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hrank : primeRank p A ≤ 2)
    (f : A →* D) (hf : Function.Surjective f)
    (hF : generalizedFitting D = pCore p D)
    (S : Subgroup D) (hS : IsPGroup 2 S) (hne : S ≠ ⊥) :
    IsCyclic ((centralizer (S : Set D)).subgroupOf (pCore p D)) := by
  classical
  let rec aux {B : Type u} [Group B] [Finite B]
      (hrankB : primeRank p B ≤ 2) (g : B →* D) (hg : Function.Surjective g) :
      IsCyclic ((centralizer (S : Set D)).subgroupOf (pCore p D)) := by
    by_cases hk : IsPGroup p g.ker
    · exact cyclic_primeCore_centralizer_of_surjective_pGroup_kernel hp hrankB g hg hk hF S hS hne
    have hnot : ¬ (Nat.card g.ker).primeFactors ⊆ p.primeFactors := by
      intro h
      exact hk ((isPGroup_iff_primeFactors_card_subset (Fact.out : p.Prime).ne_zero).mpr h)
    obtain ⟨r, hrmem, hrnot⟩ := Finset.not_subset.mp hnot
    have hr : r.Prime := Nat.prime_of_mem_primeFactors hrmem
    have hrp : r ≠ p := by
      intro he
      exact hrnot (he ▸ (Fact.out : p.Prime).mem_primeFactors_self)
    let : Fact r.Prime := ⟨hr⟩
    let R : Sylow r g.ker := Sylow.nonempty.some
    let U : Subgroup B := (R : Subgroup g.ker).map g.ker.subtype
    let N := normalizer (U : Set B)
    by_cases hN : N = ⊤
    · let : U.Normal := normalizer_eq_top_iff.mp hN
      have hUker : U ≤ g.ker := map_subtype_le _
      have hUp : IsPGroup r U := R.isPGroup'.map g.ker.subtype
      have hUne : U ≠ ⊥ := by
        intro he
        have hc : Nat.card U = 1 := card_eq_one.mpr he
        rw [show U = (R : Subgroup g.ker).map g.ker.subtype from rfl,
          card_map_of_injective g.ker.subtype_injective] at hc
        have hd := R.dvd_card_of_dvd_card (Nat.dvd_of_mem_primeFactors hrmem)
        rw [hc] at hd
        exact hr.not_dvd_one hd
      have hcop : Nat.Coprime p (Nat.card U) := by
        obtain ⟨k, hkcard⟩ := hUp.exists_card_eq
        rw [hkcard]
        exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
          (fun h => hrp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hr).mp h).symm)).pow_right k
      let gbar : B ⧸ U →* D := QuotientGroup.lift U g hUker
      have hgbar : Function.Surjective gbar :=
        QuotientGroup.lift_surjective_of_surjective U g hg hUker
      have hrbar : primeRank p (B ⧸ U) ≤ 2 :=
        (primeRank_quotient_le_of_coprime p U hcop).trans hrankB
      have hlt : Nat.card (B ⧸ U) < Nat.card B := by
        have hUcard : 1 < Nat.card U := by
          let : Nontrivial U := U.nontrivial_iff_ne_bot.mpr hUne
          exact Finite.one_lt_card
        rw [card_eq_card_quotient_mul_card_subgroup U]
        simpa using Nat.mul_lt_mul_of_pos_left hUcard (Nat.card_pos (α := B ⧸ U))
      exact aux hrbar gbar hgbar
    · have hfr : N ⊔ g.ker = ⊤ := R.normalizer_sup_eq_top
      have hmap : N.map g = ⊤ := by
        have he := congrArg (Subgroup.map g) hfr
        simpa only [Subgroup.map_sup, Subgroup.map_ker_self, sup_bot_eq,
          map_top_of_surjective g hg] using he
      have hsurj : Function.Surjective (g.comp N.subtype) :=
        MonoidHom.range_eq_top.mp (by rw [MonoidHom.range_comp, range_subtype, hmap])
      have hlt : Nat.card N < Nat.card B :=
        lt_of_le_of_ne (card_le_card_group N) (fun he => hN (N.card_eq_iff_eq_top.mp he))
      exact aux ((primeRank_subgroup_le p N).trans hrankB) (g.comp N.subtype) hsurj
  termination_by Nat.card B
  decreasing_by all_goals assumption
  exact aux hrank f hf


/-- The internal prime-core centralizer and the ambient intersection have
canonically isomorphic actual carriers. -/
def primeCoreCentralizerEquivInf {G : Type*} [Group G] (p : ℕ) (S : Subgroup G) :
    (centralizer (S : Set G)).subgroupOf (pCore p G) ≃*
      (pCore p G ⊓ centralizer (S : Set G) : Subgroup G) where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

end Theory.GroupTheory
