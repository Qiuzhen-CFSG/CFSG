module
public import Theory.GroupTheory.OddPrimeSectionCentralizers

/-!
# Reduction to a three-group kernel with the same target

The Frattini argument on a Sylow subgroup of a non-three kernel prime
reduces the covering group: a proper normalizer surjects onto the same
target, while a normal Sylow subgroup can be quotiented out through its
coprime order. Strong induction terminates at a three-group kernel.
The rank bound stays on the covering group at every step.

Source: Aschbacher--Smith, the common reduction for A.1.31(1,3),
printed pp.27--28. This specializes the already proved centralizer reduction
and exposes its actual smaller cover for clause(3).
-/

public section
open Subgroup
namespace Theory.GroupTheory.ThreeSection
universe u v

/-- Every finite rank-two source may be replaced by another rank-two source
mapping onto the same target with three-group kernel. -/
theorem exists_three_kernel_cover {D : Type u} [Group D] [Finite D]
    {E : Type v} [Group E] [Finite E]
    (hrank : primeRank 3 D ≤ 2) (f : D →* E) (hf : Function.Surjective f) :
    ∃ (B : Type u) (_ : Group B) (_ : Finite B) (g : B →* E),
      Function.Surjective g ∧ primeRank 3 B ≤ 2 ∧ IsPGroup 3 g.ker := by
  classical
  let rec aux {B : Type u} [Group B] [Finite B]
      (hrankB : primeRank 3 B ≤ 2) (g : B →* E) (hg : Function.Surjective g) :
      ∃ (C : Type u) (_ : Group C) (_ : Finite C) (q : C →* E),
        Function.Surjective q ∧ primeRank 3 C ≤ 2 ∧ IsPGroup 3 q.ker := by
    by_cases hk : IsPGroup 3 g.ker
    · exact ⟨B, inferInstance, inferInstance, g, hg, hrankB, hk⟩
    have hnot : ¬ (Nat.card g.ker).primeFactors ⊆ Nat.primeFactors 3 := by
      intro h
      exact hk ((isPGroup_iff_primeFactors_card_subset (by decide : 3 ≠ 0)).mpr h)
    obtain ⟨r, hrmem, hrnot⟩ := Finset.not_subset.mp hnot
    have hr : r.Prime := Nat.prime_of_mem_primeFactors hrmem
    have hrp : r ≠ 3 := by
      intro he
      exact hrnot (he ▸ Nat.prime_three.mem_primeFactors_self)
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
      have hcop : Nat.Coprime 3 (Nat.card U) := by
        obtain ⟨k, hkcard⟩ := hUp.exists_card_eq
        rw [hkcard]
        exact (Nat.prime_three.coprime_iff_not_dvd.mpr
          (fun h => hrp ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp h).symm)).pow_right k
      let gbar : B ⧸ U →* E := QuotientGroup.lift U g hUker
      have hgbar : Function.Surjective gbar :=
        QuotientGroup.lift_surjective_of_surjective U g hg hUker
      have hrbar : primeRank 3 (B ⧸ U) ≤ 2 :=
        (primeRank_quotient_le_of_coprime 3 U hcop).trans hrankB
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
      exact aux ((primeRank_subgroup_le 3 N).trans hrankB) (g.comp N.subtype) hsurj
  termination_by Nat.card B
  decreasing_by all_goals assumption
  exact aux hrank f hf

end Theory.GroupTheory.ThreeSection
