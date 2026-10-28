module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Preimages
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.FullImage
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.MSBlock

/-!
# The full-radical MS pair in natural S6 control

The original component and the point parabolic generate the ambient group.
Consequently the component--Baumann product is normal. B.2.19 places its
two-core in the Baumann subgroup. When the Baumann image is the full point
radical, the product maps onto S6, and its point parabolic has index fifteen
and precisely the Baumann subgroup as two-core. This gives literal MS2(a).

A characteristic subgroup of that same Baumann subgroup which is normal
in the product is also normalized by the original point parabolic. Thus
absence of the original characteristic-normal obstruction gives MS3. No
classification or whole-core reconstruction is assumed in this reduction.

Source: Aschbacher--Smith C.1.37, printed pp.141--143, using B.2.19 and
C.1.31(MS2)--(MS3), printed p.135.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.NaturalSixControl
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
open ChapterB ChapterB.BaumannArgument
open ChapterB.Offenders.Six
universe u
variable {K : Type u} [Group K] [Finite K]
variable {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
namespace SourceData
variable (d : SourceData L V T)
include d

omit [Finite K] in
theorem component_sup_point : L ⊔ d.P = ⊤ := by
  apply top_unique
  rw [← d.generation]
  exact sup_le_sup_left d.sylow_le_point L

omit [Finite K] in
/-- The actual component--Baumann product is normal in the original group. -/
theorem product_normal : (L ⊔ d.B : Subgroup K).Normal := by
  apply normalizer_eq_top_iff.mp
  apply eq_top_iff.mpr
  rw [← d.component_sup_point]
  apply sup_le (le_sup_left.trans le_normalizer)
  exact (le_inf le_normalizer_of_normal d.normalizes_B).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

theorem core_product : pCore 2 (L ⊔ d.B : Subgroup K) = (pCore 2 K).comap (L ⊔ d.B : Subgroup K).subtype :=
  pCore_subnormal_eq_comap 2 d.product_normal.isSubnormal

omit [Finite K] [L.Normal] [V.Normal] d in
omit [Finite K] [L.Normal] [V.Normal] d in
private theorem eq_of_sylowIn_of_two {A E : Subgroup K}
    (h : IsSylowSubgroupIn A E) (hp : IsPGroup 2 E) : A = E := by
  obtain ⟨S,hS⟩ := h
  have hs : (S : Subgroup E) = ⊤ := (S.is_maximal' (hp.to_subgroup ⊤) le_top).symm
  change (S : Subgroup E).map E.subtype = A at hS
  simpa only [hs,← MonoidHom.range_eq_map,range_subtype] using hS.symm

/-- The B.2.19 centralizer Sylow conclusion puts the product two-core in B. -/
theorem core_product_le_baumann (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q0 ≤ last) :
    pCore 2 (L ⊔ d.B : Subgroup K) ≤ d.B.subgroupOf (L ⊔ d.B : Subgroup K) := by
  let := d.elementary
  have hs := d.baumann_kernel_sylow hne
  rw [d.centralizer_eq_core] at hs
  have he : d.B ⊓ pCore 2 K = (L ⊔ d.B : Subgroup K) ⊓ pCore 2 K :=
    eq_of_sylowIn_of_two hs (pCore_isPGroup.to_le inf_le_right)
  intro x hx
  have hxQ : (x:K) ∈ pCore 2 K := by rw [d.core_product] at hx; exact hx
  exact (he.symm ▸ show (x:K) ∈ (L ⊔ d.B : Subgroup K) ⊓ pCore 2 K from ⟨x.property,hxQ⟩).1

noncomputable def qProduct : (L ⊔ d.B : Subgroup K) →* Model.S := d.q0.comp (L ⊔ d.B : Subgroup K).subtype

theorem product_image (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q0 ≤ last) :
    (L ⊔ d.B : Subgroup K).map d.q0 = ⊤ := by
  have ha : alternatingGroup (Fin 6) ≤ (L ⊔ d.B : Subgroup K).map d.q0 := by
    rw [← d.q0_image_component]
    exact map_mono le_sup_left
  have hd : ((L ⊔ d.B : Subgroup K).map d.q0).index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le ha
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hi | hi
  · exact index_eq_one.mp hi
  · have he := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
    have hs : ChapterB.Offenders.pairSwap 6 2 ∈ (L ⊔ d.B : Subgroup K).map d.q0 := by
      apply map_mono (show d.B ≤ L ⊔ d.B from le_sup_right)
      rw [d.baumann_image_eq_full hne]
      exact ChapterB.Offenders.Six.last_le_exceptional (subset_closure rfl)
    rw [he] at hs
    have hn : ChapterB.Offenders.pairSwap 6 2 ∉ alternatingGroup (Fin 6) := by decide
    exact (hn hs).elim

theorem qProduct_onto (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q0 ≤ last) :
    Function.Surjective d.qProduct := by
  apply MonoidHom.range_eq_top.mp
  rw [qProduct,MonoidHom.range_comp,range_subtype,d.product_image hne]

theorem qProduct_kernel : d.qProduct.ker = pCore 2 (L ⊔ d.B : Subgroup K) := by
  rw [d.core_product,← d.q0_kernel]
  rfl

/-- The point parabolic in the actual product has the original S6 index. -/
theorem point_product_index (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q0 ≤ last) :
    (d.P.subgroupOf (L ⊔ d.B : Subgroup K)).index = 15 := by
  have hp : d.P.subgroupOf (L ⊔ d.B : Subgroup K) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1.comap d.qProduct := by
    rw [d.P_eq_comap]
    rfl
  rw [hp,Subgroup.index_comap_of_surjective _ (d.qProduct_onto hne)]
  rw [← Theory.SpecificGroups.SymmetricSix.BinaryFlags.flagRelabel_duad,
    index_map_of_bijective (MulAut.conj
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.flagRelabel).bijective,
    Theory.SpecificGroups.SymmetricSix.duadStabilizer_index]

/-- Its intrinsic two-core is precisely the full Baumann subgroup. -/
theorem point_product_core (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q0 ≤ last) :
    (d.P.subgroupOf (L ⊔ d.B : Subgroup K)).pCoreIn 2 = d.B.subgroupOf (L ⊔ d.B : Subgroup K) := by
  let P := d.P.subgroupOf (L ⊔ d.B : Subgroup K)
  let B := d.B.subgroupOf (L ⊔ d.B : Subgroup K)
  have hp : IsPGroup 2 d.qProduct.ker := d.qProduct_kernel.symm ▸ pCore_isPGroup
  have hPm : P.map d.qProduct = Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1 := by
    have he : P = Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1.comap d.qProduct := by
      dsimp only [P]
      rw [d.P_eq_comap]
      rfl
    rw [he,map_comap_eq_self_of_surjective (d.qProduct_onto hne)]
  have hBm : B.map d.qProduct = Model.E := by
    rw [qProduct,← map_map,map_subgroupOf_eq_of_le (show d.B ≤ L ⊔ d.B from le_sup_right)]
    exact d.baumann_image_eq_full hne
  have hm : (P.pCoreIn 2).map d.qProduct = Model.E := by
    rw [map_pCoreIn_of_ker_isPGroup d.qProduct hp,hPm,
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1_core_eq_pointCore,
      Model.pointCore_eq_exceptional]
  have hk : d.qProduct.ker ≤ P.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes hp
    · intro j hj
      change (j : K) ∈ d.P
      apply d.core_le_point
      rw [← d.q0_kernel]
      exact hj
    · exact le_normalizer_of_normal
  have hBk : d.qProduct.ker ≤ B := d.qProduct_kernel ▸ d.core_product_le_baumann hne
  change P.pCoreIn 2 = B
  rw [← comap_map_eq_self hk,← comap_map_eq_self hBk,hm,hBm]

theorem odd_index_radical (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q0 ≤ last) :
    MSOddIndexRadical (d.B.subgroupOf (L ⊔ d.B : Subgroup K)) := by
  refine ⟨d.P.subgroupOf (L ⊔ d.B : Subgroup K),?_,?_,d.point_product_core hne⟩
  · apply lt_top_iff_ne_top.mpr
    intro ht
    have hh := d.point_product_index hne
    rw [ht,index_top] at hh
    norm_num at hh
  · rw [d.point_product_index hne]
    decide

omit [Group K] [Finite K] [L.Normal] [V.Normal] d in
omit [Group K] [Finite K] [L.Normal] [V.Normal] d in
private theorem characteristic_map_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (C : Subgroup A) (hC : C.Characteristic) :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y,hy,rfl⟩ := hx
  let b : MulAut A := e.trans (a.trans e.symm)
  refine ⟨b y,(characteristic_iff_le_comap.mp hC b) hy,?_⟩
  exact e.apply_symm_apply _

omit [Finite K] in
/-- MS3 is transported by the original point parabolic and product generation. -/
theorem characteristic_condition
    (hno : ¬ ∃ C : Subgroup d.B, C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map d.B.subtype).Normal) : MSCharacteristicCondition (d.B.subgroupOf (L ⊔ d.B : Subgroup K)) := by
  intro C hC hne hn
  let BJ := d.B.subgroupOf (L ⊔ d.B : Subgroup K)
  let e : BJ ≃* d.B := subgroupOfEquivOfLe (show d.B ≤ L ⊔ d.B from le_sup_right)
  let D := C.map e.toMonoidHom
  have hD : D.Characteristic := characteristic_map_equiv e C hC
  have hDne : D ≠ ⊥ := fun hz => hne ((C.map_eq_bot_iff_of_injective e.injective).mp hz)
  have he : D.map d.B.subtype = (C.map BJ.subtype).map (L ⊔ d.B : Subgroup K).subtype := by
    rw [map_map,map_map]
    rfl
  have hJN : L ⊔ d.B ≤ normalizer (D.map d.B.subtype : Set K) := by
    rw [he]
    have h := (C.map BJ.subtype).le_normalizer_map (L ⊔ d.B : Subgroup K).subtype
    let := hn
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using h
  have hPN : d.P ≤ normalizer (D.map d.B.subtype : Set K) := by
    let := hD
    exact d.normalizes_B.trans (normalizer_le_normalizer_characteristic_image d.B D)
  have hnormal : (D.map d.B.subtype).Normal := by
    apply normalizer_eq_top_iff.mp
    apply eq_top_iff.mpr
    rw [← d.component_sup_point]
    exact sup_le (le_sup_left.trans hJN) hPN
  exact hno ⟨D,hD,hDne,hnormal⟩

/-- The original full-image branch supplies the exact intrinsic MS2/MS3 pair. -/
theorem intrinsicMSPair_of_full_image
    (hne : ¬ (elementaryAbelianMaxJ d.R).map d.q0 ≤ last)
    (hno : ¬ ∃ C : Subgroup d.B, C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map d.B.subtype).Normal) : IntrinsicMSPair d :=
  ⟨d.odd_index_radical hne,d.characteristic_condition hno⟩

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl
