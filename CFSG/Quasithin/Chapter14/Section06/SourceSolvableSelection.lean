module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Source

/-!
# Prime-preserving descent and maximal odd-prime selection

Lift a nontrivial odd p-core of H/O2(H), take its two-residual and adjoin
the original Sylow subgroup T. Original 14.6.1(4) places this join outside M.
Minimal descent supplies an elementary minimal normal odd residual; Lagrange's
theorem retains its prime p, since the join has only the prime divisors 2 and p.
A finite maximum over all outside prime cores therefore realizes the book's
maximal-prime choice on an actual minimal solvable outside subgroup. Both T
and the selected M are unchanged throughout.

Source: Aschbacher--Smith, 14.6.11--12 and the paragraph preceding 14.6.14,
printed pp.1030--1032.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open OddNormalizer
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

/-- Descend from a nontrivial odd prime core without changing its prime. -/
theorem source_minimal_outside_of_primeCore
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) (hne : pCore p (H ⧸ pCore 2 H) ≠ ⊥) :
    ∃ J : Subgroup G, J ≤ H ∧ J ∈ Chapter3.HStar (T : Subgroup G) M ∧
      Group.IsSolvable J ∧ (p = 3 ∨ p = 5) ∧ PrimitiveResidual J p ∧
      pResidual 2 (J ⧸ pCore 2 J) ≠ ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  let P := pCore p (H ⧸ pCore 2 H)
  let A₀ := P.comap q
  let A := A₀.map H.subtype
  let X := (pResidual 2 A).map A.subtype
  have hAH : A ≤ H := map_subtype_le _
  have hHA : H ≤ normalizer (A : Set G) := by
    have hh := A₀.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hHX : H ≤ normalizer (X : Set G) :=
    hHA.trans (normalizer_le_normalizer_characteristic_image A (pResidual 2 A))
  have hAP : A₀.map q = P := by
    exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  let : Group.IsNilpotent P := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable q.ker := by
    dsimp [q]
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
    infer_instance
  let : Group.IsSolvable A₀ := isSolvable_comap_of_solvable_ker q P
  let : Group.IsSolvable A := Group.isSolvable_of_surjective
    (f := (equivMapOfInjective A₀ H.subtype H.subtype_injective).toMonoidHom)
    (equivMapOfInjective A₀ H.subtype H.subtype_injective).surjective
  let : Group.IsSolvable X := Group.isSolvable_of_surjective
    (f := (equivMapOfInjective (pResidual 2 A) A.subtype A.subtype_injective).toMonoidHom)
    (equivMapOfInjective (pResidual 2 A) A.subtype A.subtype_injective).surjective
  have hXne : X ≠ ⊥ := by
    intro hz
    have hr : pResidual 2 A = ⊥ :=
      (map_eq_bot_iff_of_injective _ A.subtype_injective).mp hz
    have hAp : IsPGroup 2 A := (isPGroup_quotient_pResidual (G := A) 2).of_injective
      (QuotientGroup.mk' (pResidual 2 A)) (by
        apply (MonoidHom.ker_eq_bot_iff _).mp
        rw [QuotientGroup.ker_mk',hr])
    have hA₀p := hAp.of_equiv (equivMapOfInjective A₀ H.subtype H.subtype_injective).symm
    have hPp : IsPGroup 2 P := hAP ▸ hA₀p.map q
    have hd := IsPGroup.disjoint_of_coprime hPp (pCore_isPGroup (p := p))
      (Nat.coprime_two_left.mpr ho)
    exact hne (disjoint_self.mp hd)
  have hout := source_lemma_14_6_1_4 hG T hempty hM hu hmany hcard e hab H hH
    X ((map_subtype_le _).trans hAH) hHX (isPPerfect_embedded_pResidual 2 A) hXne
  let C := X ⊔ (T : Subgroup G)
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  let : Group.IsSolvable C := Group.isSolvable_sup_of_normalizes X (T : Subgroup G)
    (hH.1.2.trans hHX)
  obtain ⟨J,hJ,hJC,hmin⟩ := exists_minimal_subgroup_of_mem_le
    (fun J => J ∈ Chapter1.HOutside G (T : Set G) (M : Set G)) C hout
  have hstar : J ∈ Chapter3.HStar (T : Subgroup G) M :=
    ⟨hJ,fun K hK hKJ => (hmin K hK hKJ).ge⟩
  have hs : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective (inclusion_injective hJC)
  obtain ⟨r,hr,hE,_hbound,hrne,hm⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hu hmany hcard e hab J hstar hs
  have hrp : r.Prime := by rcases hr with h | h <;> rw [h] <;> decide
  have hro : Odd r := by rcases hr with h | h <;> rw [h] <;> decide
  let : Fact r.Prime := ⟨hrp⟩
  let := hE
  have heq : r = p := by
    by_contra hnp
    have hcT : Nat.Coprime r (Nat.card (T : Subgroup G)) := by
      obtain ⟨n,hn⟩ := T.isPGroup'.exists_card_eq
      rw [hn]
      exact (Nat.coprime_two_right.mpr hro).pow_right n
    have hcA : Nat.Coprime r (Nat.card A) := by
      rw [card_map_of_injective H.subtype_injective]
      let f := q.domRestrict A₀
      have hk : IsPGroup 2 f.ker := by
        change IsPGroup 2 (q.ker.comap A₀.subtype)
        rw [show q.ker = pCore 2 H from QuotientGroup.ker_mk' _]
        exact (pCore_isPGroup (p := 2) (G := H)).comap_subtype (K := A₀)
      have hf : f.range = P := by
        change (q.comp A₀.subtype).range = P
        rw [MonoidHom.range_comp,range_subtype]
        exact hAP
      have hfp : IsPGroup p f.range := hf.symm ▸ pCore_isPGroup
      obtain ⟨n,hn⟩ := hk.exists_card_eq
      obtain ⟨m,hm⟩ := hfp.exists_card_eq
      rw [←f.ker.card_mul_index,index_ker,hn,hm]
      exact ((Nat.coprime_two_right.mpr hro).pow_right n).mul_right
        ((hrp.coprime_iff_not_dvd.mpr (fun hd => hnp ((Nat.prime_dvd_prime_iff_eq hrp hp).mp hd))).pow_right m)
    have hcX := hcA.coprime_dvd_right (card_dvd_of_le (show X ≤ A from map_subtype_le _))
    have hcC : Nat.Coprime r (Nat.card C) := by
      have hh := ((T : Subgroup G).subgroupOf C).card_mul_index
      rw [Nat.card_congr (subgroupOfEquivOfLe
        (show (T : Subgroup G) ≤ C from le_sup_right)).toEquiv] at hh
      change Nat.card (T : Subgroup G) * (T : Subgroup G).relIndex C = Nat.card C at hh
      rw [relIndex_sup_of_normalizes X (T : Subgroup G) (hH.1.2.trans hHX)] at hh
      rw [←hh]
      exact hcT.mul_right (hcX.coprime_dvd_right ((T : Subgroup G).subgroupOf X).index_dvd_card)
    have hd : r ∣ Nat.card (pResidual 2 (J ⧸ pCore 2 J)) :=
      (IsElementaryAbelian.isPGroup r _).card_eq_or_dvd.resolve_left
        (fun h => hrne ((eq_bot_iff_card _).mpr h))
    exact (hrp.coprime_iff_not_dvd.mp hcC) (hd.trans
      ((pResidual 2 (J ⧸ pCore 2 J)).card_subgroup_dvd_card.trans
        ((pCore 2 J).index_dvd_card.trans (card_dvd_of_le hJC))))
  subst r
  exact ⟨J,hJC.trans (sup_le ((map_subtype_le _).trans hAH) hH.1.2),hstar,hs,hr,⟨hE,hm⟩,hrne⟩

/-- The maximal-prime choice ranges over all outside subgroups, while its
witness is minimal outside and has an elementary minimal normal residual. -/
theorem source_maximal_primitive_outside_of_solvable
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hs : Group.IsSolvable H) :
    ∃ (J : Subgroup G) (_hJ : J ∈ Chapter3.HStar (T : Subgroup G) M),
      Group.IsSolvable J ∧ ∃ p : ℕ, (p = 3 ∨ p = 5) ∧ PrimitiveResidual J p ∧
        pResidual 2 (J ⧸ pCore 2 J) ≠ ⊥ ∧ MaximalOddPrime (T : Subgroup G) M p := by
  classical
  let primes : ℕ → Prop := fun p => p.Prime ∧ Odd p ∧
    ∃ K ∈ Chapter1.HOutside G (T : Set G) (M : Set G), pCore p (K ⧸ pCore 2 K) ≠ ⊥
  have bound : ∀ p, primes p → p ≤ Nat.card G := by
    rintro p ⟨hp,_ho,K,_hK,hne⟩
    let : Fact p.Prime := ⟨hp⟩
    have hd : p ∣ Nat.card (pCore p (K ⧸ pCore 2 K)) :=
      (pCore_isPGroup (p := p)).card_eq_or_dvd.resolve_left
        (fun h => hne ((eq_bot_iff_card _).mpr h))
    exact Nat.le_of_dvd Nat.card_pos (hd.trans
      ((pCore p (K ⧸ pCore 2 K)).card_subgroup_dvd_card.trans
        ((pCore 2 K).index_dvd_card.trans K.card_subgroup_dvd_card)))
  have hex : ∃ p, primes p := by
    obtain ⟨J,hJ,hJH,hmin⟩ := exists_minimal_subgroup_of_mem_le
      (fun J => J ∈ Chapter1.HOutside G (T : Set G) (M : Set G)) H hH
    have hstar : J ∈ Chapter3.HStar (T : Subgroup G) M :=
      ⟨hJ,fun K hK hKJ => (hmin K hK hKJ).ge⟩
    let := hs
    have hsJ : Group.IsSolvable J := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective hJH)
    obtain ⟨p,hp,hE,_hr,hne,_hmin⟩ := source_solvable_minimal_elementary_residual
      hG T hempty hM hu hmany hcard e hab J hstar hsJ
    have hpp : p.Prime := by rcases hp with h | h <;> rw [h] <;> decide
    have ho : Odd p := by rcases hp with h | h <;> rw [h] <;> decide
    let : Fact p.Prime := ⟨hpp⟩
    let := hE
    refine ⟨p,hpp,ho,J,hJ,?_⟩
    intro hz
    have hle : pResidual 2 (J ⧸ pCore 2 J) ≤ pCore p (J ⧸ pCore 2 J) :=
      le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup p _⟩
    exact hne (bot_unique (hz ▸ hle))
  obtain ⟨r,hr⟩ := hex
  let p := Nat.findGreatest primes (Nat.card G)
  obtain ⟨hp,ho,K,hK,hne⟩ := Nat.findGreatest_spec (bound r hr) hr
  obtain ⟨J,_hJK,hJ,hsJ,hp35,hprim,hres⟩ := source_minimal_outside_of_primeCore
    hG T hempty hM hu hmany hcard e hab K hK p hp ho hne
  refine ⟨J,hJ,hsJ,p,hp35,hprim,hres,?_⟩
  intro L hL q hq hoq hQ
  exact Nat.le_findGreatest (bound q ⟨hq,hoq,L,hL,hQ⟩) ⟨hq,hoq,L,hL,hQ⟩
end CFSG.Quasithin.Chapter14.Section06
