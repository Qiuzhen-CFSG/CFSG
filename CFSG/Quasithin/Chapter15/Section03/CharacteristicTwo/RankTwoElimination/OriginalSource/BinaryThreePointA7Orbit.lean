module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointCoreNormalizer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointAlternatingModels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Layers

/-!
# The original core has stabilizer of index fifteen in the A7 lift

The actual full Sylow at the point puts its two-core N inside the original
join J=LS. Thus N normalizes the original commutator core Q. In the A7 row,
Q lies in N and [N,L]=Q. The lift of A7 cannot normalize Q by the marked
characteristic eight-section obstruction. Its normalizer image is therefore
a proper overgroup of the original order168 subgroup B, hence equals B.
Pulling back through the same point quotient gives N_{Ktilde}(Q)=NL and
index15. No characteristicity of Q in N, or characteristic-two assertion
for the entire point centralizer, is used.

This is an exact orbit constraint, not an exclusion of the A7 carrier.
Source: Aschbacher--Smith15.3.23, pp.1128--1129, with MS93(4.5)(v), p.895.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem a7_proper_overgroup_eq
    {B D K : Subgroup G} (hBK : B ≤ K) (hBD : B ≤ D) (hDK : D ≤ K)
    (hcard : Nat.card B = 168) (a : K ≃* alternatingGroup (Fin 7))
    (hproper : D ≠ K) : D = B ∧ B.relIndex K = 15 := by
  let B₀ := B.subgroupOf K
  let D₀ := D.subgroupOf K
  have hB : Nat.card (B₀.map a.toMonoidHom) = 168 := by
    rw [card_map_of_injective a.injective,
      Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv]
    exact hcard
  have hD : D₀.map a.toMonoidHom ≠ ⊤ := by
    intro ht
    have he : D₀ = ⊤ := by
      apply map_injective (f := a.toMonoidHom) a.injective
      rw [ht, ← MonoidHom.range_eq_map, a.toMonoidHom.range_eq_top_of_surjective a.surjective]
    apply hproper
    exact le_antisymm hDK (subgroupOf_eq_top.mp he)
  have he := alternatingGroup.SevenThreeSection.eq_of_le_of_card
    (B₀.map a.toMonoidHom) (D₀.map a.toMonoidHom) hB
    (map_mono (comap_mono hBD)) hD
  have he₀ : D₀ = B₀ := map_injective a.injective he
  have hDB : D = B := by
    have hh := congrArg (map K.subtype) he₀
    simpa only [B₀,D₀,map_subgroupOf_eq_of_le hBK,map_subgroupOf_eq_of_le hDK] using hh
  have hK : Nat.card K = 2520 := by
    rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.card_fin,Nat.factorial]
  have hB₀ : Nat.card B₀ = 168 :=
    (Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv).trans hcard
  have hi := B₀.card_mul_index
  rw [hB₀,hK] at hi
  exact ⟨hDB,by change B₀.index = 15; omega⟩

private theorem point_a7_core_stabilizer
    (L Q C : Subgroup G) (hLC : L ≤ C)
    (e : (L ⧸ pCore 2 L) ≃* PSL(3,ZMod 2))
    (K : Subgroup (C ⧸ pCore 2 C))
    (hBK : (L.subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)) ≤ K)
    (a : K ≃* alternatingGroup (Fin 7))
    (hLQ : L ≤ normalizer Q) (hNQ : C.pCoreIn 2 ≤ normalizer Q)
    (hnot : ¬ ((K.comap (QuotientGroup.mk' (pCore 2 C))).map C.subtype) ≤ normalizer Q) :
    let A := (K.comap (QuotientGroup.mk' (pCore 2 C))).map C.subtype
    normalizer Q ⊓ A = C.pCoreIn 2 ⊔ L ∧
      (normalizer Q ⊓ A).relIndex A = 15 := by
  let q := QuotientGroup.mk' (pCore 2 C)
  let H := L.subgroupOf C
  let B := H.map q
  let A₀ := K.comap q
  let W := (normalizer Q).subgroupOf C ⊓ A₀
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hkerA : q.ker ≤ A₀ := by
    intro x hx
    change q x ∈ K
    rw [MonoidHom.mem_ker.mp hx]
    exact K.one_mem
  have hkerW : q.ker ≤ W := by
    intro x hx
    refine ⟨?_,hkerA hx⟩
    apply hNQ
    exact mem_map_of_mem C.subtype ((QuotientGroup.ker_mk' _).le hx)
  have hHW : H ≤ W := by
    intro x hx
    exact ⟨hLQ hx,hBK (mem_map_of_mem q hx)⟩
  have hWK : W.map q ≤ K := (map_mono (show W ≤ A₀ from inf_le_right)).trans
    (map_comap_le q K)
  have hproper : W.map q ≠ K := by
    intro he
    have hWA : W = A₀ := by
      have hh := congrArg (comap q) he
      rw [comap_map_eq,sup_eq_left.mpr hkerW] at hh
      exact hh
    apply hnot
    rintro x ⟨y,hy,rfl⟩
    exact ((hWA.symm ▸ hy : y ∈ W)).1
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hkH : IsPGroup 2 (q.subgroupMap H).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let i : H ≃* L := subgroupOfEquivOfLe hLC
  let eH := (QuotientGroup.congr _ _ i (pCore_map_iso 2 i)).trans e
  let eB := ((q.subgroupMap H).pCoreQuotientEquiv
    (q.subgroupMap_surjective H) hkH).symm.trans eH
  have hcard : Nat.card B = 168 := (binary_three_alternating_seven_placement hBK eB a).2.1
  obtain ⟨hWB,hindex⟩ := a7_proper_overgroup_eq hBK (map_mono hHW) hWK hcard a hproper
  have hW : W = H ⊔ pCore 2 C := by
    have hh := congrArg (comap q) hWB
    rw [comap_map_eq,sup_eq_left.mpr hkerW] at hh
    change W = (H.map q).comap q at hh
    rwa [comap_map_eq,QuotientGroup.ker_mk'] at hh
  have hmapW : W.map C.subtype = normalizer Q ⊓ A₀.map C.subtype := by
    rw [map_inf _ _ _ C.subtype_injective,subgroupOf_map_subtype,inf_assoc,
      inf_eq_right.mpr (map_subtype_le A₀)]
  have hnormal : normalizer Q ⊓ A₀.map C.subtype = C.pCoreIn 2 ⊔ L := by
    rw [←hmapW,hW,Subgroup.map_sup,map_subgroupOf_eq_of_le hLC,sup_comm]
    rfl
  have hi : W.relIndex A₀ = 15 := by
    have hh := relIndex_map_map q W A₀
    rw [hWB,map_comap_eq_self_of_surjective hq,
      sup_eq_left.mpr hkerW,sup_eq_left.mpr hkerA] at hh
    exact hh.symm.trans hindex
  refine ⟨hnormal,?_⟩
  rw [←hmapW,relIndex_map_map_of_injective W A₀ C.subtype_injective]
  exact hi

/-- The full original point source gives the exact normalizer and index15
for the unchanged core in the A7 carrier lift. The full Sylow supplies the
point-kernel normalization; no action or normalizer conclusion is assumed. -/
theorem binary_three_source_a7_core_stabilizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (a : K ≃* alternatingGroup (Fin 7)) :
    let C := centralizer ({z} : Set G)
    let N := C.pCoreIn 2
    let Q := LinearThree.commutatorCore c.L
    let A := (K.comap (QuotientGroup.mk' (pCore 2 C))).map C.subtype
    Q ≤ N ∧ ⁅N,c.L⁆ = Q ∧ normalizer Q ⊓ A = N ⊔ c.L ∧
      (normalizer Q ⊓ A).relIndex A = 15 := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let J := c.L ⊔ d.S
  let Q := LinearThree.commutatorCore c.L
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  have hQN : Q ≤ N := binary_three_alternating_seven_commutator_core_le c.L C hLC e K hBK a
  have hNS : N ≤ d.S := hP ▸ pCoreIn_le_sylow C P
  have hNJ : N ≤ J.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 C) (hNS.trans le_sup_right)
      (hLS.trans (C.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image C (pCore 2 C))))
  have hJL : J ≤ normalizer c.L :=
    (normal_subgroupOf_iff_le_normalizer (show c.L ≤ J from le_sup_left)).mp b.component_normal
  have hJQ : J ≤ normalizer Q := hJL.trans (normalizer_le_normalizer_commutatorCore c.L)
  have hQL : ⁅Q,c.L⁆ = Q := by
    have he : (BinaryMS.commutatorCore (c.L.subgroupOf J)).map J.subtype = Q :=
      LinearThree.CoreActions.sourceQ_map_subtype (show c.L ≤ J from le_sup_left) b.component
    have hh := congrArg (map J.subtype) b.commutatorCore_idempotent
    rw [map_commutator,he,map_subgroupOf_eq_of_le (show c.L ≤ J from le_sup_left)] at hh
    exact hh
  have hNL : ⁅N,c.L⁆ = Q := le_antisymm
    ((commutator_mono hNJ le_rfl).trans
      (overgroup_core_commutator_eq d c (le_sup_right.trans hJL)).le)
    (hQL.symm.le.trans (commutator_mono hQN le_rfl))
  have hnot := binary_three_source_alternating_core_not_normalized
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS K hBK 7 (Or.inl rfl) a
  obtain ⟨hn,hi⟩ := point_a7_core_stabilizer c.L Q C hLC e K hBK a
    (le_sup_left.trans hJQ) ((hNS.trans le_sup_right).trans hJQ) hnot
  exact ⟨hQN,hNL,hn,hi⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
