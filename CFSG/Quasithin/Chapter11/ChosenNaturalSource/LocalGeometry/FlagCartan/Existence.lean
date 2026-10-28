module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Existence of the literal source Cartan

Write T_L = T intersect L O₂(LT). The intersection T intersect L is
Sylow in L because T normalizes L. It lies in N_L(T_L), and this
normalizer preserves it: T_L intersect L = T intersect L. Thus the
restricted Sylow subgroup is normal, and Schur--Zassenhaus supplies its
odd Hall complement. Mapping this complement back to G constructs the
source Cartan without any assumed flag, torus or model geometry.

Flag normalization and the prime-rank calculation are separate model
obligations. This theorem only establishes the actual Hall existence.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
Chapter 11 setup, printed p.759.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

omit [Finite G] in
/-- The original Sylow intersection lies in the source T_L. -/
theorem sylow_intersection_le_sourceTL : (T : Subgroup G) ⊓ L ≤ sourceTL T L :=
  le_inf inf_le_left (inf_le_right.trans le_sup_left)

omit [Finite G] in
/-- Intersecting the source T_L with L recovers the original Sylow intersection. -/
theorem sourceTL_inf_component : sourceTL T L ⊓ L = (T : Subgroup G) ⊓ L := by
  apply le_antisymm
  · exact inf_le_inf_right L inf_le_left
  · exact le_inf (sylow_intersection_le_sourceTL (T := T) (L := L)) inf_le_right

omit [Finite G] in
/-- The literal source normalizer preserves its Sylow intersection with L. -/
theorem cartanNormalizer_normalizes_intersection :
    cartanNormalizer T L ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
  rw [← sourceTL_inf_component]
  exact (le_inf inf_le_right (inf_le_left.trans L.le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

include D in
/-- The chosen source component admits an actual Hall odd-order Cartan. -/
theorem exists_cartan : ∃ X : Subgroup G, IsCartan T L X := by
  let N := cartanNormalizer T L
  let H := N.subgroupOf L
  obtain ⟨P, hP⟩ := NormalSylowQuotientAction.intersection_sylow T L
    D.sylow_normalizes_component
  have hPN : (P : Subgroup L) ≤ H := by
    intro p hp
    have ht : (p : G) ∈ T := by rw [hP] at hp; exact hp
    exact ⟨p.property, (sourceTL T L).le_normalizer
      (sylow_intersection_le_sourceTL ⟨ht, p.property⟩)⟩
  let Q := P.subtype hPN
  let : (Q : Subgroup H).Normal := by
    constructor
    intro q hq h
    change (h : L) * q * (h : L)⁻¹ ∈ (P : Subgroup L)
    rw [hP]
    have hqP : q.val ∈ (P : Subgroup L) := hq
    have hqT : (q.val : G) ∈ T := by rw [hP] at hqP; exact hqP
    exact ((cartanNormalizer_normalizes_intersection (T := T) (L := L)
      h.property) (q.val : G)).mp ⟨hqT, q.val.property⟩ |>.1
  obtain ⟨U, hU⟩ := exists_right_complement'_of_coprime Q.card_coprime_index
  have hUH : IsHallSubgroup OddHall.oddPrimes U := by
    constructor
    · intro p hp he
      have hc : Nat.card U = (Q : Subgroup H).index := hU.card_right
      exact Q.not_dvd_index (by simpa only [hc, he] using hp)
    · intro p hp hpodd
      have hi : U.index = Nat.card Q := hU.index_eq_card
      obtain ⟨n, hn⟩ := Q.isPGroup'.exists_card_eq
      exact hpodd (Nat.prime_eq_prime_of_dvd_pow p.property Nat.prime_two
        (by rwa [hi, hn] at hp))
  let e : H ≃* N := subgroupOfEquivOfLe (show N ≤ L from inf_le_left)
  let XN := U.map e.toMonoidHom
  refine ⟨XN.map N.subtype, map_subtype_le _, ?_⟩
  have hh : (XN.map N.subtype).subgroupOf N = XN :=
    comap_map_eq_self_of_injective N.subtype_injective XN
  rw [hh]
  constructor
  · intro p hp
    apply hUH.p_in_pi_of_p_dvd_card p
    rwa [Nat.card_congr (U.equivMapOfInjective e.toMonoidHom e.injective).toEquiv]
  · intro p hp
    apply hUH.p_in_pi_of_p_dvd_index p
    exact hp.trans (index_map_dvd U e.surjective)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
