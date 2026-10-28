module

public import Stellmacher.Recognition.NormalEightSeparatedCentralizerData

/-!
# The closure inside the original Sylow subgroup

The elementary normal closure in a centralizer supplement is transported back
to the original Sylow subgroup. The centralizer of the noncentral involution
has index two, normalizes the transported closure, and is its full normalizer
when normal elementary eights are excluded.

These facts isolate the local group identification in the order-eight branch
of Janko–Thompson, Math. Z. 113 (1970), Lemma 3.1, printed p.388;
refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedClosureEight
open Subgroup NormalEightSeparatedCentralizers
open scoped IsMulCommutative
variable {G : Type*} [Group G]

/-- The selected normal closure, viewed in the original Sylow subgroup. -/
public abbrev closureInSylow {S : Sylow 2 G} {W : Subgroup S} {i : S}
    (d : CentralizerSetup S W i) : Subgroup S :=
  ((d.closure.map d.H.subtype).map
    (centralizer ({(i : G)} : Set G)).subtype).subgroupOf (S : Subgroup G)

public theorem closureImage_le_sylow {S : Sylow 2 G} {W : Subgroup S} {i : S}
    (d : CentralizerSetup S W i) :
    (d.closure.map d.H.subtype).map
      (centralizer ({(i : G)} : Set G)).subtype ≤ S := by
  rintro x ⟨v, hv, rfl⟩
  have ht := d.closure_le hv
  rw [d.sylow_eq] at ht
  exact ht

public theorem closureInSylow_elementary {S : Sylow 2 G} {W : Subgroup S} {i : S}
    (d : CentralizerSetup S W i) : IsElementaryAbelian 2 (closureInSylow d) := by
  let : IsElementaryAbelian 2 d.closure := d.elementary
  let : IsElementaryAbelian 2 (d.closure.map d.H.subtype) :=
    IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 ((d.closure.map d.H.subtype).map
      (centralizer ({(i : G)} : Set G)).subtype) := IsElementaryAbelian.map_subtype
  exact IsElementaryAbelian.subgroupOf (closureImage_le_sylow d)

public theorem card_closureInSylow {S : Sylow 2 G} {W : Subgroup S} {i : S}
    (d : CentralizerSetup S W i) : Nat.card (closureInSylow d) = Nat.card d.closure := by
  rw [Nat.card_congr (subgroupOfEquivOfLe (closureImage_le_sylow d)).toEquiv,
    card_map_of_injective (centralizer ({(i : G)} : Set G)).subtype_injective,
    card_map_of_injective d.H.subtype_injective]

public theorem closureInSylow_le_centralizer {S : Sylow 2 G} {W : Subgroup S} {i : S}
    (d : CentralizerSetup S W i) : closureInSylow d ≤ centralizer ({i} : Set S) := by
  rintro x ⟨v, _, hv⟩
  apply mem_centralizer_singleton_iff.mpr
  apply Subtype.ext
  have h := mem_centralizer_singleton_iff.mp v.property
  change (v : G) = (x : G) at hv
  change (x : G) * (i : G) = (i : G) * (x : G)
  rwa [hv] at h

/-- The intrinsic involution centralizer normalizes the transported closure. -/
public theorem centralizer_le_normalizer_closureInSylow
    {S : Sylow 2 G} {W : Subgroup S} {i : S} (d : CentralizerSetup S W i) :
    centralizer ({i} : Set S) ≤ normalizer (closureInSylow d : Set S) := by
  apply le_normalizer_iff.mpr
  intro t ht x hx
  let tC : centralizer ({(i : G)} : Set G) :=
    ⟨t, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ht))⟩
  have htT : tC ∈ (d.T : Subgroup (centralizer ({(i : G)} : Set G))) := by
    rw [d.sylow_eq]
    exact t.property
  let tH : d.H := ⟨tC, d.sylow_le htT⟩
  obtain ⟨xC, ⟨xH, hxH, rfl⟩, he⟩ := hx
  refine ⟨(tH * xH * tH⁻¹ : d.H), ?_, ?_⟩
  · exact mem_map_of_mem _ ((inferInstance : d.closure.Normal).conj_mem xH hxH tH)
  · change (t : G) * (xH : G) * (t : G)⁻¹ = (t : G) * (x : G) * (t : G)⁻¹
    change (xH : G) = (x : G) at he
    rw [he]

/-- The original four is contained in the transported normal closure. -/
public theorem four_le_closureInSylow
    {S : Sylow 2 G} {W : Subgroup S} [IsElementaryAbelian 2 W]
    {i : S} (hiW : i ∈ W) (d : CentralizerSetup S W i) : W ≤ closureInSylow d := by
  intro w hw
  have hwi : Commute w i := by
    exact congrArg Subtype.val (mul_comm (⟨w, hw⟩ : W) ⟨i, hiW⟩)
  let wC : centralizer ({(i : G)} : Set G) :=
    ⟨w, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hwi.eq)⟩
  have hwU : wC ∈ (W.map (S : Subgroup G).subtype).subgroupOf
      (centralizer ({(i : G)} : Set G)) := mem_map_of_mem _ hw
  let wH : d.H := ⟨wC, d.four_le hwU⟩
  exact ⟨wC, ⟨wH, le_normalClosure hwU, rfl⟩, rfl⟩

/-- The selected local Sylow is the intrinsic involution centralizer. -/
public def sylowCentralizerEquiv
    {S : Sylow 2 G} {W : Subgroup S} {i : S} (d : CentralizerSetup S W i) :
    d.T ≃* centralizer ({i} : Set S) where
  toFun t := ⟨⟨t.val, by
    exact (SetLike.ext_iff.mp d.sylow_eq t.val).mp t.property⟩, mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp t.val.property))⟩
  invFun t := ⟨⟨t.val, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp t.property))⟩, by
    rw [d.sylow_eq]
    exact t.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable [Finite G]

/-- Fixing the noncentral involution fixes the entire normal four. -/
public theorem centralizer_involution_eq_four
    (S : Sylow 2 G) (W : Subgroup S) [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z : S) (hzW : z ∈ W) (hzC : z ∈ center S)
    (hz : orderOf z = 2) (i : S) (hiW : i ∈ W) (hi : orderOf i = 2)
    (hiC : i ∉ center S) : centralizer ({i} : Set S) = centralizer (W : Set S) := by
  let : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour W := ⟨hW, IsElementaryAbelian.exponent_eq_prime⟩
  have hi1 : (⟨i, hiW⟩ : W) ≠ 1 := by
    intro h
    have he : i = 1 := congrArg Subtype.val h
    simp [he] at hi
  have hz1 : (⟨z, hzW⟩ : W) ≠ 1 := by
    intro h
    have he : z = 1 := congrArg Subtype.val h
    simp [he] at hz
  have hiz : (⟨i, hiW⟩ : W) ≠ ⟨z, hzW⟩ := by
    intro h
    have he : i = z := congrArg Subtype.val h
    exact hiC (he ▸ hzC)
  apply le_antisymm ?_ (centralizer_le (Set.singleton_subset_iff.mpr hiW))
  intro g hg x hx
  have hgi : Commute g i := mem_centralizer_singleton_iff.mp hg
  have hgz : Commute g z := mem_center_iff.mp hzC g
  let w : W := ⟨x, hx⟩
  by_cases h1 : w = 1
  · have he : x = 1 := congrArg Subtype.val h1
    simp [he]
  by_cases hiw : w = ⟨i, hiW⟩
  · have he : x = i := congrArg Subtype.val hiw
    exact he ▸ hgi.eq.symm
  by_cases hzw : w = ⟨z, hzW⟩
  · have he : x = z := congrArg Subtype.val hzw
    exact he ▸ hgz.eq.symm
  have he : x = i * z := congrArg Subtype.val
    (IsKleinFour.eq_mul_of_ne_all hi1 hz1 hiz h1 hiw hzw)
  rw [he]
  exact (hgi.mul_right hgz).eq.symm

public theorem centralizer_involution_index
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z : S) (hzW : z ∈ W) (hzC : z ∈ center S)
    (hz : orderOf z = 2) (i : S) (hiW : i ∈ W) (hi : orderOf i = 2)
    (hiC : i ∉ center S) : (centralizer ({i} : Set S)).index = 2 := by
  have hb : (centralizer ({i} : Set S)).index ≤ 2 := by
    rw [centralizer_involution_eq_four S W hW z hzW hzC hz i hiW hi hiC]
    exact centralizer_index_le_two_of_normal_four S.isPGroup' W hW
  have hn := (centralizer ({i} : Set S)).index_ne_zero_of_finite
  have hone : (centralizer ({i} : Set S)).index ≠ 1 := by
    intro h
    exact hiC (centralizer_eq_top_iff_subset.mp (index_eq_one.mp h) (Set.mem_singleton i))
  omega

/-- A normal elementary eight is the only obstruction to the full normalizer equality. -/
public theorem normalizer_closureInSylow_eq
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z : S) (hzW : z ∈ W) (hzC : z ∈ center S)
    (hz : orderOf z = 2) (i : S) (hiW : i ∈ W) (hi : orderOf i = 2)
    (hiC : i ∉ center S)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (d : CentralizerSetup S W i) (hc : Nat.card d.closure = 8) :
    normalizer (closureInSylow d : Set S) = centralizer ({i} : Set S) := by
  have hle := centralizer_le_normalizer_closureInSylow d
  by_contra hne
  have hlt := index_strictAnti (lt_of_le_of_ne hle (Ne.symm hne))
  rw [centralizer_involution_index S W hW z hzW hzC hz i hiW hi hiC] at hlt
  have hn := (normalizer (closureInSylow d : Set S)).index_ne_zero_of_finite
  have htop : normalizer (closureInSylow d : Set S) = ⊤ := index_eq_one.mp (by omega)
  exact hno ⟨closureInSylow d, normalizer_eq_top_iff.mp htop,
    closureInSylow_elementary d, by rw [card_closureInSylow, hc]⟩

end Stellmacher.Recognition.NormalEightSeparatedClosureEight
