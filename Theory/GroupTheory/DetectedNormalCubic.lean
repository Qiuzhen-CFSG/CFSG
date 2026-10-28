module
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.OddCyclicThreeNormalizer
public import Theory.GroupTheory.CyclicSubgroupNormalizer

/-!
# A detected normal cubic in a three-group

A normal subgroup A of order three in a three-group P is central. If a
homomorphism is injective on A and its image has order at most three, A
splits off the literal kernel. At three-rank at most two this kernel is
cyclic. Moreover a cyclic overgroup of A is A itself: any nontrivial
intersection with the kernel would contain the unique cubic line A.

Source application: Aschbacher–Smith 14.7.21(1), printed p.1050. The
normalizer factor acts on the original L/O₂(L), detecting its point cubic.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {P H : Type*} [Group P] [Finite P] [Group H] [Finite H]

/-- A normal cubic detected by a homomorphism with image of order at most
three splits off its literal kernel in a three-group. -/
theorem detected_normal_cubic_product
    (hP : IsPGroup 3 P) (A : Subgroup P) [A.Normal]
    (hc : Nat.card A = 3) (f : P →* H)
    (hi : Function.Injective (f.comp A.subtype)) (hr : Nat.card f.range ≤ 3) :
    A ⊔ f.ker = ⊤ ∧ Disjoint A f.ker ∧ A ≤ center P := by
  have hcop : Nat.Coprime 2 (Nat.card P) := by
    obtain ⟨n,hn⟩ := hP.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_right n
  have hz : A ≤ center P := by
    have hh := commutator_eq_bot_iff_le_centralizer.mp
      (commutator_eq_bot_of_odd_normalizes_card_three A ⊤ hc
        (by simpa only [Nat.card_congr (topEquiv : (⊤ : Subgroup P) ≃* P).toEquiv] using hcop)
        le_normalizer_of_normal)
    simpa only [coe_top, centralizer_univ] using hh
  have hAc : Nat.card (A.map f) = 3 := by
    have he : (f.comp A.subtype).range = A.map f := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [←he, ←Nat.card_congr (MonoidHom.ofInjective hi).toEquiv]
    exact hc
  have he : A.map f = f.range :=
    eq_of_le_of_card_ge (map_le_range f A) (hr.trans_eq hAc.symm)
  have hgen : A ⊔ f.ker = ⊤ := by
    rw [←comap_map_eq,he]
    exact top_unique (fun x _ => ⟨x,rfl⟩)
  have hd : Disjoint A f.ker := by
    apply disjoint_def.mpr
    intro x hx hk
    have hh : (⟨x,hx⟩ : A) = 1 := hi (by simpa using hk)
    exact congrArg (fun a : A => (a : P)) hh
  exact ⟨hgen,hd,hz⟩

/-- The complement is cyclic when the three-rank is at most two. -/
theorem detected_normal_cubic_kernel_cyclic
    (hP : IsPGroup 3 P) (hrank : primeRank 3 P ≤ 2)
    (A : Subgroup P) [A.Normal] (hc : Nat.card A = 3) (f : P →* H)
    (hi : Function.Injective (f.comp A.subtype)) (hr : Nat.card f.range ≤ 3) :
    IsCyclic f.ker := by
  obtain ⟨hgen,hd,hz⟩ := detected_normal_cubic_product hP A hc f hi hr
  have hAr : 1 ≤ primeRank 3 A := by
    by_contra h
    have h0 : primeRank 3 A = 0 := by omega
    exact (PrimeRank.eq_zero_iff_not_dvd_card.mp h0) (hc ▸ dvd_rfl)
  have he := primeRank_sup_eq_add_of_disjoint_commuting
    A f.ker hd (hz.trans (center_le_centralizer _)) 3
  have hh : primeRank 3 (A ⊔ f.ker : Subgroup P) ≤ 2 := by
    rw [hgen, Theory.GroupTheory.primeRank_equiv 3 (topEquiv : (⊤ : Subgroup P) ≃* P)]
    exact hrank
  have hk : primeRank 3 f.ker ≤ 1 := by omega
  exact (hP.to_subgroup f.ker).isCyclic_of_odd_of_elementary_card_le (by decide)
    (fun E hE => by
      let := hE
      exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hk E)

/-- A cyclic overgroup of a detected cubic is that cubic itself. -/
theorem cyclic_eq_detected_cubic
    (hP : IsPGroup 3 P) (A : Subgroup P) (hc : Nat.card A = 3)
    (f : P →* H) (hi : Function.Injective (f.comp A.subtype))
    (hr : Nat.card f.range ≤ 3) (D : Subgroup P) [IsCyclic D] (hAD : A ≤ D) : D = A := by
  have hk : Disjoint D f.ker := by
    by_contra hd
    have hne : D ⊓ f.ker ≠ ⊥ := fun he => hd (disjoint_iff.mpr he)
    have hp : 3 ∣ Nat.card (D ⊓ f.ker : Subgroup P) := by
      obtain ⟨n,hn⟩ := (hP.to_subgroup (D ⊓ f.ker)).exists_card_eq
      have hn0 : n ≠ 0 := by
        intro hh
        apply hne
        apply card_eq_one.mp
        simpa [hh] using hn
      rw [hn]
      exact dvd_pow_self 3 hn0
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(D ⊓ f.ker : Subgroup P)) 3 hp
    have hxa : (x : P) ∈ A := by
      have h : (⟨x,x.property.1⟩ : D) ^ Nat.card (A.subgroupOf D) = 1 := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hAD).toEquiv,hc]
        have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
        exact Subtype.ext (congrArg (fun z : (D ⊓ f.ker : Subgroup P) => (z : P)) hx3)
      exact mem_of_pow_card_eq_one_in_cyclic (A.subgroupOf D) h
    have hx1 : (⟨x,hxa⟩ : A) = 1 := hi (by simpa using x.property.2)
    have hx1' : x = 1 := Subtype.ext (congrArg (fun z : A => (z : P)) hx1)
    rw [hx1',orderOf_one] at hx
    omega
  have hfi : Function.Injective (f.comp D.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    exact Subtype.ext (hk.le_bot ⟨x.property,hx⟩)
  have hDc : Nat.card D ≤ 3 :=
    (Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv).le.trans
      ((Nat.card_le_card_of_injective
        (inclusion (show (f.comp D.subtype).range ≤ f.range from by
          rintro y ⟨x,rfl⟩
          exact ⟨x,rfl⟩)) (inclusion_injective _)).trans hr)
  exact (eq_of_le_of_card_ge hAD (hDc.trans_eq hc.symm)).symm
end Subgroup
