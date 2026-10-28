module

public import Stellmacher.Recognition.Parrott.SylowCoreSelectionData
public import Stellmacher.Recognition.Parrott.DerivedLocalCenters

/-!
# Selecting the fourth central commutator row

Write H = C_G(z), J = O₂(H), and E for the actual ambient image of J′.
The supplied derived basis generates the elementary abelian group E of order
32. Adjoining an involution at most doubles subgroup order, so deleting v
leaves U = ⟨z,t,u,w⟩ of order exactly 16. The centralizer pairing formula
gives |C_J(U)| = 64, while C_G(E) = E has order 32. Choose c in C_J(U)
outside E. It cannot commute with v, since U and v generate E. Its
commutator with v lies in Z(J) = ⟨z⟩, and hence equals z.

All supplied coordinates are retained; no choice of the remaining core
relations or assumption of core generation is used.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.679, equations (9)–(10), and the pairing formula on pp.673–674.
-/

open Subgroup
open scoped commutatorElement
namespace Stellmacher.Recognition

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem binary_join_bound (B A : Subgroup G) [IsElementaryAbelian 2 B]
    (hAB : A ≤ B) (x : G) (hx : x ∈ B) :
    Nat.card (A ⊔ zpowers x : Subgroup G) ≤ 2 * Nat.card A := by
  by_cases hxA : x ∈ A
  · rw [sup_eq_left.mpr (zpowers_le.mpr hxA)]
    omega
  · rw [card_sup_zpowers_of_normalizing_involution A x
      (elemPow_eq_one_of_isElementaryAbelian x hx) hxA]
    apply Subgroup.centralizer_le_normalizer
    intro a ha
    exact setLike_mul_comm (s := B) (hAB ha) hx

omit [Finite G] in
private theorem closure_insert_eq (x : G) (s : Set G) :
    closure (insert x s) = closure s ⊔ zpowers x := by
  rw [show insert x s = s ∪ {x} by ext; simp,
    Subgroup.closure_union, ← zpowers_eq_closure]

/-- The fourth row of the central commutator pairing, with all supplied
coordinates unchanged. -/
public theorem ParrottSylowThreeGeneratorData.exists_fourth_commutator_row
    {z : G} (h : ParrottCentralizerHypotheses z)
    {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
    (f : ParrottSylowThreeGeneratorData n) :
    let H := centralizer ({z} : Set G)
    let J := (pCore 2 H).map H.subtype
    ∃ c : G, c ∈ J ∧
      Tits.parrottCommutator c f.u = 1 ∧
      Tits.parrottCommutator c f.w = 1 ∧
      Tits.parrottCommutator c n.t = 1 ∧
      Tits.parrottCommutator c n.v = z := by
  classical
  intro H J
  let K := pCore 2 H
  let embed := H.subtype.comp K.subtype
  let E := (commutator K).map embed
  let U := closure ({z, n.t, f.u, f.w} : Set G)
  obtain ⟨hZ, _, _, _, hUpper, hElem, hDcard, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 (commutator K) := hElem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map embed
  have hEcard : Nat.card E = 32 := by
    rw [card_map_of_injective (K := commutator K) (f := embed)
      (H.subtype_injective.comp K.subtype_injective)]
    exact hDcard
  have hbasis : closure ({z, n.t, n.v, f.u, f.w} : Set G) = E := f.derived_basis
  have hzE : z ∈ E := by rw [← hbasis]; exact subset_closure (by simp)
  have htE : n.t ∈ E := by rw [← hbasis]; exact subset_closure (by simp)
  have huE : f.u ∈ E := by rw [← hbasis]; exact subset_closure (by simp)
  have hwE : f.w ∈ E := by rw [← hbasis]; exact subset_closure (by simp)
  have hvE : n.v ∈ E := by rw [← hbasis]; exact subset_closure (by simp)
  have hUE : U ≤ E := by
    apply (Subgroup.closure_le E).mpr
    simpa only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      using And.intro hzE (And.intro htE (And.intro huE hwE))
  have hUjoin : U ⊔ zpowers n.v = E := by
    rw [← closure_insert_eq, ← hbasis]
    congr 1
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hbound : Nat.card U ≤ 16 := by
    have hw : Nat.card (zpowers f.w) ≤ 2 := by
      have hc := binary_join_bound E ⊥ bot_le f.w hwE
      simpa using hc
    have huw := binary_join_bound E (zpowers f.w) (zpowers_le.mpr hwE) f.u huE
    have htuw := binary_join_bound E (zpowers f.w ⊔ zpowers f.u)
      (sup_le (zpowers_le.mpr hwE) (zpowers_le.mpr huE)) n.t htE
    have hztuw := binary_join_bound E ((zpowers f.w ⊔ zpowers f.u) ⊔ zpowers n.t)
      (sup_le (sup_le (zpowers_le.mpr hwE) (zpowers_le.mpr huE))
        (zpowers_le.mpr htE)) z hzE
    change Nat.card (closure ({z, n.t, f.u, f.w} : Set G)) ≤ 16
    rw [closure_insert_eq, closure_insert_eq, closure_insert_eq, ← zpowers_eq_closure]
    omega
  have hUcard : Nat.card U = 16 := by
    have hc := binary_join_bound E U hUE n.v hvE
    rw [hUjoin, hEcard] at hc
    omega
  let C := J ⊓ centralizer (U : Set G)
  have hCcard : Nat.card C = 64 := by
    have hc := parrott_core_inf_centralizer_card z h U
      (zpowers_le.mpr (subset_closure (by simp))) hUE
    change Nat.card U * Nat.card C = 1024 at hc
    rw [hUcard] at hc
    omega
  have hnot : ¬ C ≤ E := by
    intro hle
    have hc := card_le_of_le hle
    rw [hCcard, hEcard] at hc
    omega
  obtain ⟨c, hcC, hcE⟩ := SetLike.not_le_iff_exists.mp hnot
  have hcomm (a : G) (ha : a ∈ U) : Tits.parrottCommutator c a = 1 :=
    (Tits.parrottCommutator_eq_one_iff _ _).mpr ((hcC.2 a ha).symm)
  refine ⟨c, hcC.1, hcomm f.u (subset_closure (by simp)),
    hcomm f.w (subset_closure (by simp)),
    hcomm n.t (subset_closure (by simp)), ?_⟩
  have hne : Tits.parrottCommutator c n.v ≠ 1 := by
    intro heq
    apply hcE
    rw [← show centralizer (E : Set G) = E from parrott_derived_centralizer z h]
    have hUc : U ≤ centralizer ({c} : Set G) := by
      intro a ha
      exact mem_centralizer_singleton_iff.mpr (hcC.2 a ha)
    have hEc : E ≤ centralizer ({c} : Set G) := by
      rw [← hUjoin]
      exact sup_le hUc (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        ((Tits.parrottCommutator_eq_one_iff _ _).mp heq).symm.eq))
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hEc ha)
  have hrow : Tits.parrottCommutator c n.v ∈ zpowers z := by
    have hcentral : ⁅commutator K, (⊤ : Subgroup K)⁆ ≤ center K := by
      rw [hUpper]
      simpa only [Subgroup.upperCentralSeries_one] using
        commutator_upperCentralSeries_top_le K 1
    obtain ⟨vK, hvK, hvG⟩ := hvE
    obtain ⟨cH, hcK, hcG⟩ := hcC.1
    let cK : K := ⟨cH, hcK⟩
    have hm := mem_map_of_mem embed (hcentral (commutator_mem_commutator
      ((commutator K).inv_mem hvK) (show cK⁻¹ ∈ (⊤ : Subgroup K) from mem_top _)))
    rw [hZ] at hm
    have heq : embed ⁅vK⁻¹, cK⁻¹⁆ = (Tits.parrottCommutator c n.v)⁻¹ := by
      simp only [commutatorElement_def, map_mul, map_inv, inv_inv,
        Tits.parrottCommutator, mul_inv_rev]
      change (embed vK)⁻¹ * (H.subtype cH)⁻¹ * embed vK * H.subtype cH = _
      rw [hvG, hcG, mul_assoc, mul_assoc]
    rw [heq] at hm
    simpa only [inv_inv] using (zpowers z).inv_mem hm
  rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hrow
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hrow
  have hi2 : i < 2 := Finset.mem_range.mp hi
  interval_cases i
  · exact (hne (by simpa using heq.symm)).elim
  · simpa using heq.symm

end Stellmacher.Recognition
