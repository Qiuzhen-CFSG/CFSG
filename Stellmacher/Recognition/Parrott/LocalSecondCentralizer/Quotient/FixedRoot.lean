module

public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.Quotient.Geometry
public import Theory.GroupAction.CoprimeCentralizerLift

/-!
# The excluded root and the compatible three-action

The fixed subgroup of the actual Sylow image Y under the supplied Q is
exactly ⟨v⟩. Indeed C_K(Q)=⟨b⟩ has order four and the second transfer
excludes b from L; the intersection with Y therefore contains only 1 and b²=v.
This retains the compatible Q and root, for the quotient normalizer calculation.

Source: Parrott (1972), Lemma 8, printed p.683, C_Y(Q)=⟨v⟩.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondTransferData
variable {G : Type*} [Group G] {z : G}
  {d : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData d}
  (t : ParrottSecondTransferData n)

public theorem excluded_root_not_mem_sylow_image :
    t.b ∉ (t.S : Subgroup t.L).map t.embedding := by
  rintro ⟨a, _, he⟩
  exact t.b_not_mem ⟨(a : t.M), a.property, he⟩

/-- Odd order puts the supplied three-group inside both literal transfer kernels. -/
public theorem three_le_embedding_range [Finite G] :
    (n.Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype ≤ t.embedding.range := by
  let N := normalizer (d.F : Set G)
  let A := (n.Q : Subgroup N).map N.subtype
  let C := centralizer ({n.v} : Set G)
  let : t.M.Normal := t.M_normal
  let : t.L.Normal := t.L_normal
  have hAC : A ≤ C := fun a ha => mem_centralizer_singleton_iff.mpr (n.v_fixed a ha)
  have hAc : Nat.card A = 3 :=
    (card_map_of_injective N.subtype_injective).trans n.three_card
  have hAM : A.subgroupOf C ≤ t.M := by
    apply relIndex_eq_one.mp
    apply Nat.eq_one_of_dvd_coprimes (show Nat.Coprime 2 3 by decide)
    · simpa only [t.M_index] using
        relIndex_dvd_index_of_normal (H := t.M) (K := A.subgroupOf C)
    · have hc : Nat.card (A.subgroupOf C) = 3 :=
        (Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv).trans hAc
      exact hc ▸ relIndex_dvd_card t.M (A.subgroupOf C)
  have hAL : (A.subgroupOf C).subgroupOf t.M ≤ t.L := by
    apply relIndex_eq_one.mp
    apply Nat.eq_one_of_dvd_coprimes (show Nat.Coprime 2 3 by decide)
    · simpa only [t.L_index] using relIndex_dvd_index_of_normal
        (H := t.L) (K := (A.subgroupOf C).subgroupOf t.M)
    · have hc : Nat.card ((A.subgroupOf C).subgroupOf t.M) = 3 := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hAM).toEquiv,
          Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv, hAc]
      exact hc ▸ relIndex_dvd_card t.L ((A.subgroupOf C).subgroupOf t.M)
  intro a ha
  exact ⟨⟨⟨⟨a, hAC ha⟩, hAM ha⟩, hAL ha⟩, rfl⟩

/-- The compatible three-group normalizes the actual Sylow image. -/
public theorem three_le_sylow_image_normalizer [Finite G] :
    (n.Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype ≤
        normalizer ((t.S : Subgroup t.L).map t.embedding : Set G) := by
  let N := normalizer (d.F : Set G)
  let K := pCore 2 N
  let U := omega₁ K (p := 2)
  let W := U.map (N.subtype.comp K.subtype)
  have hNW : N ≤ normalizer (W : Set G) := by
    let B := U.map K.subtype
    let : U.Characteristic := omega₁_characteristic K
    let : B.Normal := ConjAct.normal_of_characteristic_of_normal
    have hh := le_normalizer_map (H := B) N.subtype
    rw [normalizer_eq_top] at hh
    simpa only [← MonoidHom.range_eq_map, range_subtype, B, W, map_map] using hh
  change _ ≤ normalizer ((t.S : Subgroup t.L).map
    ((centralizer ({n.v} : Set G)).subtype.comp (t.M.subtype.comp t.L.subtype)) : Set G)
  rw [t.S_image]
  intro a ha
  have haL := t.three_le_embedding_range ha
  have haLG : a ∈ t.L.map ((centralizer ({n.v} : Set G)).subtype.comp t.M.subtype) := by
    obtain ⟨l, rfl⟩ := haL
    exact ⟨(l : t.M), l.property, rfl⟩
  apply mem_normalizer_iff.mpr
  intro x
  exact and_congr (mem_normalizer_iff.mp (hNW (map_subtype_le _ ha)) x)
    (mem_normalizer_iff.mp (le_normalizer haLG) x)

/-- The same Q used to define the excluded root fixes just the prescribed line in Y. -/
public theorem sylow_image_three_fixed [Finite G] :
    (t.S : Subgroup t.L).map t.embedding ⊓
      centralizer ((n.Q : Subgroup (normalizer (d.F : Set G))).map
        (normalizer (d.F : Set G)).subtype : Set G) = zpowers n.v := by
  classical
  let Y := (t.S : Subgroup t.L).map t.embedding
  have hvY : n.v ∈ Y := t.elementary_le_sylow_image n.v_mem_inf.2
  apply le_antisymm
  · intro x hx
    have hxb : x ∈ zpowers t.b := t.core_fixed ▸
      (show x ∈ (pCore 2 (normalizer (d.F : Set G))).map
          (normalizer (d.F : Set G)).subtype ⊓
          centralizer ((n.Q : Subgroup (normalizer (d.F : Set G))).map
            (normalizer (d.F : Set G)).subtype : Set G) from
        ⟨n.omega_le_core (t.sylow_image_le_omega hx.1), hx.2⟩)
    rw [mem_zpowers_iff_mem_range_orderOf, t.b_order] at hxb
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hxb
    have hr4 : r < 4 := Finset.mem_range.mp hr
    interval_cases r
    · simp
    · have hm : t.b ^ 1 ∈ Y := hx.1
      rw [pow_one] at hm
      exact False.elim (t.excluded_root_not_mem_sylow_image hm)
    · rw [t.b_sq]
      exact mem_zpowers n.v
    · have hb4 : t.b ^ 4 = 1 := t.b_order ▸ pow_orderOf_eq_one t.b
      have hprod : t.b ^ 3 * t.b = 1 := by rw [← pow_succ, hb4]
      have hbY : t.b ∈ Y := by
        rw [eq_inv_of_mul_eq_one_right hprod]
        exact Y.inv_mem hx.1
      exact False.elim (t.excluded_root_not_mem_sylow_image hbY)
  · exact zpowers_le.mpr ⟨hvY, n.v_fixed⟩

/-- The compatible three-action has no nonidentity fixed coset in Y/⟨v⟩,
expressed with the original ambient elements and commutators. -/
public theorem sylow_image_mem_line_of_three_fixed_modulo [Finite G]
    {x : G} (hx : x ∈ (t.S : Subgroup t.L).map t.embedding)
    (hfixed : ∀ a ∈ (n.Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype,
        MulAut.conj a x / x ∈ zpowers n.v) :
    x ∈ zpowers n.v := by
  let Y := (t.S : Subgroup t.L).map t.embedding
  let V := zpowers n.v
  let A := (n.Q : Subgroup (normalizer (d.F : Set G))).map
    (normalizer (d.F : Set G)).subtype
  have hVY : V ≤ Y := zpowers_le.mpr (t.elementary_le_sylow_image n.v_mem_inf.2)
  have hYV : Y ≤ centralizer (V : Set G) := by
    rw [show V = zpowers n.v from rfl, zpowers_eq_closure, centralizer_closure]
    exact (map_le_range t.embedding _).trans t.embedding_range_le_centralizer
  let : (V.subgroupOf Y).Normal :=
    (normal_subgroupOf_iff_le_normalizer hVY).mpr
      (hYV.trans (Subgroup.centralizer_le_normalizer _))
  have hAV : A ≤ normalizer (V : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    rw [show V = zpowers n.v from rfl, zpowers_eq_closure, centralizer_closure]
    exact fun a ha => mem_centralizer_singleton_iff.mpr (n.v_fixed a ha)
  have hcop : Nat.Coprime (Nat.card A) (Nat.card V) := by
    have hAcard : Nat.card A = 3 :=
      (card_map_of_injective (normalizer (d.F : Set G)).subtype_injective).trans n.three_card
    rw [hAcard, show Nat.card V = 2 from (Nat.card_zpowers n.v).trans n.v_order]
    decide
  have hh := Y.mem_centralizer_sup_of_coprime_fixed_coset V A hVY
    t.three_le_sylow_image_normalizer hAV hcop x hx hfixed
  change x ∈ ((t.S : Subgroup t.L).map t.embedding ⊓ centralizer (A : Set G)) ⊔
    zpowers n.v at hh
  rw [t.sylow_image_three_fixed] at hh
  exact (show zpowers n.v ⊔ zpowers n.v ≤ zpowers n.v from sup_le le_rfl le_rfl) hh

end Stellmacher.Recognition.ParrottSecondTransferData
