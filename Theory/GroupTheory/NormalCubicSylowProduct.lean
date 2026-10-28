module
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.OddCyclicThreeNormalizer
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.NormalClosure

/-!
# Sylow three-subgroups with a detected normal cubic

A normal subgroup of order three is central in a three-group. If a map to
S₃ × S₃ is injective on this subgroup, one coordinate remains injective;
its image is the whole coordinate image of the three-group. The coordinate
kernel is consequently a direct complement. Three-rank at most two forces
this complement to be cyclic. A surjection onto S₃ × S₃ ensures its order
is a positive power of three.

Source application: the cubic row of Aschbacher--Smith15.2.3(1)(iii),
printed p.1105, applied to the original group modulo its two-core.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {P : Type*} [Group P] [Finite P]

private theorem cubic_coordinate {A : Type*} [Group A]
    (hc : Nat.card A = 3) (f : A →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
    (hi : Function.Injective f) :
    Function.Injective ((MonoidHom.fst _ _).comp f) ∨
    Function.Injective ((MonoidHom.snd _ _).comp f) := by
  let : IsSimpleGroup A := isSimpleGroup_of_prime_card hc
  let a := (MonoidHom.fst _ _).comp f
  let b := (MonoidHom.snd _ _).comp f
  rcases (inferInstance : a.ker.Normal).eq_bot_or_eq_top with ha | ha
  · exact Or.inl ((MonoidHom.ker_eq_bot_iff a).mp ha)
  · right
    apply (injective_iff_map_eq_one b).mpr
    intro x hx
    apply hi
    rw [map_one]
    apply Prod.ext
    · exact (show a x = 1 from MonoidHom.mem_ker.mp (ha ▸ mem_top x))
    · exact hx

private theorem cubic_threeGroup_product (hP : IsPGroup 3 P)
    (hr : primeRank 3 P ≤ 2) (hdiv : 9 ∣ Nat.card P)
    (A : Subgroup P) [A.Normal] (hc : Nat.card A = 3)
    (f : P →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
    (hi : Function.Injective (f.comp A.subtype)) :
    ∃ n : ℕ, 1 ≤ n ∧ Nonempty
      (P ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod (3 ^ n))) := by
  have hcop : Nat.Coprime 2 (Nat.card P) := by
    obtain ⟨k,hk⟩ := hP.exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 2 3).pow_right k
  have hcentral : A ≤ center P := by
    have hh := commutator_eq_bot_iff_le_centralizer.mp
      (commutator_eq_bot_of_odd_normalizes_card_three A ⊤ hc
        (by simpa only [Nat.card_congr (topEquiv : (⊤ : Subgroup P) ≃* P).toEquiv] using hcop)
        le_normalizer_of_normal)
    simpa only [coe_top,centralizer_univ] using hh
  obtain ⟨g,hg⟩ : ∃ g : P →* Equiv.Perm (Fin 3), Function.Injective (g.comp A.subtype) := by
    rcases cubic_coordinate hc (f.comp A.subtype) hi with h | h
    · exact ⟨(MonoidHom.fst _ _).comp f,h⟩
    · exact ⟨(MonoidHom.snd _ _).comp f,h⟩
  have hAc : Nat.card (A.map g) = 3 := by
    have he : (g.comp A.subtype).range = A.map g := by rw [MonoidHom.range_comp,range_subtype]
    rw [← he,← Nat.card_congr (MonoidHom.ofInjective hg).toEquiv]
    exact hc
  obtain ⟨S,hS⟩ := (hP.of_surjective g.rangeRestrict g.rangeRestrict_surjective).exists_le_sylow
  have hSc : Nat.card S = 3 := by
    rw [S.card_eq_multiplicity, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide +kernel
  have hArange : A.map g = g.range := by
    apply eq_of_le_of_card_ge (map_le_range g A)
    exact (Nat.card_le_card_of_injective (inclusion hS) (inclusion_injective hS)).trans (by rw [hSc,hAc])
  have hgen : A ⊔ g.ker = ⊤ := by
    rw [← comap_map_eq, hArange]
    apply top_unique
    intro x _
    exact ⟨x,rfl⟩
  have hd : Disjoint A g.ker := by
    apply disjoint_def.mpr
    intro a ha hk
    have hh : (⟨a,ha⟩ : A) = 1 := hg (by simpa using hk)
    exact congrArg (fun a : A => (a : P)) hh
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A g.ker hd
    (hcentral.trans (center_le_centralizer _))
  let eP : A × g.ker ≃* P := e.trans ((MulEquiv.subgroupCongr hgen).trans topEquiv)
  have hAr : 1 ≤ primeRank 3 A := by
    by_contra h
    have hz : primeRank 3 A = 0 := by omega
    exact (PrimeRank.eq_zero_iff_not_dvd_card.mp hz) (hc ▸ dvd_rfl)
  have hKr : primeRank 3 g.ker ≤ 1 := by
    have he := Theory.GroupTheory.primeRank_equiv 3 eP
    rw [primeRank_prod_eq_add] at he
    omega
  let : IsCyclic g.ker := (hP.to_subgroup g.ker).isCyclic_of_odd_of_elementary_card_le (by decide)
    (fun E hE => by
      let := hE
      exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hKr E)
  obtain ⟨n,hn⟩ := (hP.to_subgroup g.ker).exists_card_eq
  have hnpos : 1 ≤ n := by
    by_contra hn0
    have hn0 : n = 0 := by omega
    have hp := Nat.card_congr eP.toEquiv
    rw [Nat.card_prod,hc,hn,hn0] at hp
    norm_num at hp
    rw [←hp] at hdiv
    norm_num at hdiv
  let : NeZero (3 ^ n) := ⟨pow_ne_zero _ (by decide)⟩
  refine ⟨n,hnpos,⟨eP.symm.trans (MulEquiv.prodCongr ?_ ?_)⟩⟩
  · exact mulEquivOfPrimeCardEq hc (by simp)
  · exact mulEquivOfCyclicCardEq (by simpa using hn)
/-- A normal cubic detected by a symmetric-three-square quotient splits every Sylow three-subgroup. -/
theorem normal_cubic_sylow_three_product
    {H : Type*} [Group H] [Finite H]
    (hr : primeRank 3 H ≤ 2)
    (A : Subgroup H) [A.Normal] (hc : Nat.card A = 3)
    (f : H →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
    (hf : Function.Surjective f) (hi : Function.Injective (f.comp A.subtype))
    (P : Sylow 3 H) :
    ∃ n : ℕ, 1 ≤ n ∧ Nonempty
      (P ≃* Multiplicative (ZMod 3) × Multiplicative (ZMod (3 ^ n))) := by
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hc)
  have hAP : A ≤ (P : Subgroup H) := hA3.le_sylow_of_normal P
  let B := A.subgroupOf (P : Subgroup H)
  have hBc : Nat.card B = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv).trans hc
  let g := f.comp (P : Subgroup H).subtype
  have hgi : Function.Injective (g.comp B.subtype) := by
    intro x y he
    have hh : (⟨(x : P),x.property⟩ : A) = ⟨(y : P),y.property⟩ := hi he
    exact Subtype.ext (Subtype.ext (congrArg (fun a : A => (a : H)) hh))
  have hdiv : 9 ∣ Nat.card P := by
    let Q := P.mapSurjective hf
    have hQc : Nat.card Q = 9 := by
      rw [Q.card_eq_multiplicity,SymmetricThreeProduct.card_group]
      decide +kernel
    have hh := card_dvd_of_surjective (f.subgroupMap (P : Subgroup H))
      (f.subgroupMap_surjective (P : Subgroup H))
    change Nat.card Q ∣ Nat.card P at hh
    rwa [hQc] at hh
  exact cubic_threeGroup_product P.isPGroup'
    ((Theory.GroupTheory.primeRank_le_of_injective 3 (P : Subgroup H).subtype (P : Subgroup H).subtype_injective).trans hr)
    hdiv B hBc g hgi

end Subgroup
