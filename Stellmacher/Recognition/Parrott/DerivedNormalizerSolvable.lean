module

public import Stellmacher.Recognition.Parrott.DerivedNormalizer

/-!
# The derived normalizer from its own solvability

Parrott's derived-core normalizer calculation needs only the solvability of
that particular normalizer. Its action on the elementary group of order 32
has kernel of order 32 and image order 320n, where n is 1, 11, 21 or 31.
The existing automorphism subgroup exclusions force n=1.

This local form lets the quasithin source supply solvability directly, without
requiring the N₂ condition on every two-local subgroup of the ambient group.
Source: Parrott (1972), Lemma 2, printed p.673.
-/

open Subgroup
namespace Stellmacher.Recognition

/-- Solvability of the actual derived-core normalizer suffices in Lemma 2. -/
public theorem parrott_derived_normalizer_of_solvable
    {G : Type*} [Group G] [Finite G]
    (z : G) (h : ParrottCentralizerHypotheses z)
    (hsolv : Group.IsSolvable
      (normalizer (((commutator (pCore 2 (centralizer ({z} : Set G)))).map
        ((centralizer ({z} : Set G)).subtype.comp
          (pCore 2 (centralizer ({z} : Set G))).subtype)) : Set G))) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    normalizer (E : Set G) = H := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let DH := D.map J.subtype
  let E := D.map (H.subtype.comp J.subtype)
  let N := normalizer (E : Set G)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  change N = H
  obtain ⟨n,hn,hNcard⟩ := parrott_derived_normalizer_card z h
  obtain ⟨_,_,_,_,_,hElem,hDcard,_⟩ := parrott_centralizer_structure z h
  change IsElementaryAbelian 2 D at hElem
  let : IsElementaryAbelian 2 D := hElem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have hEcard : Nat.card E = 32 :=
    (card_map_of_injective (K := D) (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)).trans hDcard
  have hHN : H ≤ N := by
    let : DH.Characteristic := inferInstance
    have hnorm := le_normalizer_map (H := DH) H.subtype
    rw [normalizer_eq_top] at hnorm
    simpa only [← MonoidHom.range_eq_map, range_subtype, DH, map_map] using hnorm
  let : Group.IsSolvable N := hsolv
  let f : N →* MulAut E := E.normalizerMonoidHom
  let K := f.range
  have hKsolv : Group.IsSolvable K :=
    Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hker : Nat.card f.ker = 32 := by
    rw [normalizerMonoidHom_ker, parrott_derived_centralizer z h]
    exact (Nat.card_congr (subgroupOfEquivOfLe (H := E) le_normalizer).toEquiv).trans hEcard
  have hKcard : Nat.card K = 320 * n := by
    have hc := f.ker.card_mul_index
    rw [index_ker,hker,hNcard] at hc
    change 32 * Nat.card K = 10240 * n at hc
    omega
  have hn1 : n = 1 := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · rfl
    · exact (not_eleven_dvd_card_automorphism_thirtytwo hEcard K
        (by rw [hKcard]; decide)).elim
    · exact (Theory.GroupTheory.not_card6720_of_solvable_aut32 hEcard K hKsolv
        (by simpa using hKcard)).elim
    · exact (not_card9920_of_solvable_aut32 hEcard K hKsolv
        (by simpa using hKcard)).elim
  have hHcard : Nat.card H = 10240 := (h.card_and_solvable z).1
  apply (eq_of_le_of_card_ge hHN _).symm
  rw [hNcard,hn1,hHcard]

end Stellmacher.Recognition
