module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Pointwise normalizers of cubic pairs generating A₄

An order-three subgroup of A₄ meets its commutator four-group trivially.
Consequently its normalizer centralizes it. Two such subgroups generating
A₄ have trivial common normalizer because A₄ is centerless. In a direct
product A₄ × K their common normalizer is therefore the second factor.

The final theorem keeps an arbitrary ambient embedding and the literal
subgroup inclusions. It is used for the root-four normalizer calculation
in Aschbacher, *Sporadic Groups* (1994), 47.5, printed p.263. No finite
permutation enumeration or source-recognition assertion is needed.
-/

@[expose] public section
namespace Theory.SpecificGroups.Alternating.FourPairFixer
open Subgroup
open scoped commutatorElement
abbrev A4 := alternatingGroup (Fin 4)

private theorem norm_central_of_disjoint {G : Type*} [Group G]
    (P : Subgroup G) (h : Disjoint P (_root_.commutator G)) :
    normalizer (P : Set G) ≤ centralizer (P : Set G) := by
  intro g hg
  apply mem_centralizer_iff.mpr
  intro x hx
  apply (commutatorElement_eq_one_iff_mul_comm.mp ?_).symm
  have hp : ⁅g,x⁆ ∈ P := P.mul_mem ((mem_normalizer_iff.mp hg x).mp hx) (P.inv_mem hx)
  have hc : ⁅g,x⁆ ∈ _root_.commutator G :=
    commutator_mem_commutator (mem_top g) (mem_top x)
  exact (disjoint_iff.mp h).le ⟨hp, hc⟩

/-- An order-three subgroup embeds in the abelianization of A₄. -/
theorem normalizer_three_le_centralizer (P : Subgroup A4) (hP : Nat.card P = 3) :
    normalizer (P : Set A4) ≤ centralizer (P : Set A4) := by
  apply norm_central_of_disjoint
  apply disjoint_of_coprime_natCard
  rw [hP, ← alternatingGroup.kleinFour_eq_commutator (by norm_num : Nat.card (Fin 4) = 4),
    alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num)]
  decide

/-- A cubic generating pair of A₄ has trivial pointwise normalizer. -/
theorem pair_normalizer_eq_bot (P Q : Subgroup A4)
    (hP : Nat.card P = 3) (hQ : Nat.card Q = 3) (hPQ : P ⊔ Q = ⊤) :
    normalizer (P : Set A4) ⊓ normalizer (Q : Set A4) = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  have hP' := normalizer_three_le_centralizer P hP hg.1
  have hQ' := normalizer_three_le_centralizer Q hQ hg.2
  have h : P ⊔ Q ≤ centralizer ({g} : Set A4) := by
    apply sup_le
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hP' x hx)
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hQ' x hx)
  have hz : g ∈ center A4 := mem_center_iff.mpr (fun x => by
    have := h (hPQ ▸ (mem_top x : x ∈ (⊤ : Subgroup A4)))
    exact (mem_centralizer_singleton_iff.mp this))
  rwa [alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 4))] at hz


variable {H K : Type*} [Group H] [Group K]

/-- The same calculation in any group actually isomorphic to A₄. -/
theorem pair_normalizer_of_equiv (e : H ≃* A4) (P Q : Subgroup H)
    (hP : Nat.card P = 3) (hQ : Nat.card Q = 3) (hPQ : P ⊔ Q = ⊤) :
    normalizer (P : Set H) ⊓ normalizer (Q : Set H) = ⊥ := by
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_inf _ _ _ e.injective, map_equiv_normalizer_eq, map_equiv_normalizer_eq, Subgroup.map_bot]
  apply pair_normalizer_eq_bot
  · rwa [card_map_of_injective e.injective]
  · rwa [card_map_of_injective e.injective]
  · rw [← Subgroup.map_sup, hPQ, map_top_of_surjective _ e.surjective]

private theorem norm_prod_eq (P : Subgroup H) (Q : Subgroup K) :
    normalizer (P.prod Q : Set (H × K)) =
      (normalizer (P : Set H)).prod (normalizer (Q : Set K)) := by
  ext g
  simp only [Subgroup.mem_prod, Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    constructor
    · intro x
      simpa using h (x, 1)
    · intro x
      simpa using h (1, x)
  · rintro ⟨hP, hQ⟩ ⟨x,y⟩
    exact (hP x).and (hQ y)

/-- The common normalizer of a cubic generating pair in the first factor. -/
theorem product_pair_normalizers (e : H ≃* A4) (P Q : Subgroup H)
    (hP : Nat.card P = 3) (hQ : Nat.card Q = 3) (hPQ : P ⊔ Q = ⊤) :
    normalizer (P.prod (⊥ : Subgroup K) : Set (H × K)) ⊓
      normalizer (Q.prod (⊥ : Subgroup K) : Set (H × K)) =
        (⊥ : Subgroup H).prod (⊤ : Subgroup K) := by
  have hp := pair_normalizer_of_equiv e P Q hP hQ hPQ
  have hn : normalizer (↑(⊥ : Subgroup K) : Set K) = ⊤ := normalizer_eq_top_iff.mpr inferInstance
  rw [norm_prod_eq, norm_prod_eq, hn]
  ext x
  have he := SetLike.ext_iff.mp hp x.1
  simpa only [mem_inf, mem_prod, mem_top, and_true, mem_bot] using he


variable {G : Type*} [Group G]

/-- An ambient pair fixer is the second factor of a compatible product
normalizer. The containing subgroup and its inclusion into G are literal. -/
theorem pair_normalizer_second_factor (X Y N : Subgroup G)
    (hJN : X ⊔ Y ≤ N)
    (hFN : normalizer (X : Set G) ⊓ normalizer (Y : Set G) ≤ N)
    (eJ : (X ⊔ Y : Subgroup G) ≃* A4)
    (e : N ≃* ((X ⊔ Y : Subgroup G) × K))
    (he : ∀ j : (X ⊔ Y : Subgroup G), e (inclusion hJN j) = (j, 1))
    (hX : Nat.card X = 3) (hY : Nat.card Y = 3) :
    normalizer (X : Set G) ⊓ normalizer (Y : Set G) =
      ((⊥ : Subgroup (X ⊔ Y : Subgroup G)).prod (⊤ : Subgroup K)).map
        (N.subtype.comp e.symm.toMonoidHom) := by
  let J := X ⊔ Y
  have coords (S : Subgroup G) (hS : S ≤ J) :
      (S.subgroupOf N).map e.toMonoidHom = (S.subgroupOf J).prod (⊥ : Subgroup K) := by
    ext a
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hsJ : (s : G) ∈ J := hS hs
      have hh := he ⟨s, hsJ⟩
      change e s = (⟨s, hsJ⟩, 1) at hh
      change e s ∈ (S.subgroupOf J).prod (⊥ : Subgroup K)
      rw [hh]
      exact ⟨hs, rfl⟩
    · rintro ⟨ha, hb⟩
      refine ⟨inclusion hJN a.1, ha, ?_⟩
      change e (inclusion hJN a.1) = a
      rw [he]
      exact Prod.ext rfl hb.symm
  have hc : ((normalizer (X : Set G) ⊓ normalizer (Y : Set G)).subgroupOf N).map
      e.toMonoidHom = (⊥ : Subgroup J).prod (⊤ : Subgroup K) := by
    change ((normalizer (X : Set G)).subgroupOf N ⊓
      (normalizer (Y : Set G)).subgroupOf N).map e.toMonoidHom = _
    rw [map_inf _ _ _ e.injective,
      subgroupOf_normalizer_eq (le_sup_left.trans hJN),
      subgroupOf_normalizer_eq (le_sup_right.trans hJN),
      map_equiv_normalizer_eq, map_equiv_normalizer_eq,
      coords X le_sup_left, coords Y le_sup_right]
    apply product_pair_normalizers eJ
    · rw [Nat.card_congr (subgroupOfEquivOfLe (show X ≤ J from le_sup_left)).toEquiv, hX]
    · rw [Nat.card_congr (subgroupOfEquivOfLe (show Y ≤ J from le_sup_right)).toEquiv, hY]
    · rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hc' : ((⊥ : Subgroup J).prod (⊤ : Subgroup K)).map e.symm.toMonoidHom =
      (normalizer (X : Set G) ⊓ normalizer (Y : Set G)).subgroupOf N :=
    (map_symm_eq_iff_map_eq _).mpr hc
  rw [← map_map, hc', map_subgroupOf_eq_of_le hFN]

end Theory.SpecificGroups.Alternating.FourPairFixer
