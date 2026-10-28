module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.FirstStabilizer
public import Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.LocalSubgroups.NativePlaneFlags
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.OverlapIndices

/-!
# The actual pair-hexad flag in the original plane group

An order-5760 subgroup of native M22 contains a full Sylow two-subgroup
and is intransitive on its twenty-two points. The proved Sylow-orbit
coverage places it in a pair or hexad stabilizer; orders exclude the pair
and give equality with the hexad stabilizer. Intersecting an order-11520
subgroup of Aut(M22) with the inner group, then using uniqueness of the
invariant six-point set, identifies the whole subgroup with the full
stabilizer of that SAME native hexad.

For the original three-space, both its core and cubic Sylow normalize it.
Their join is the full cubic lift. The established plane-line order then
identifies its literal projection image with a pair stabilizer, and both
original subgroups are the exact preimages under the original cubic map.
The index-fifteen flag forces the normal hexad two-kernel into the pair
stabilizer. Its free action outside the hexad proves that the pair lies
inside that hexad. No change of quotient marking is made.

The original Mathieu application supplies the point-plane order and flag
index, giving these overlaps simultaneously with the retained trio and
sextet markings. Todd splitting remains a separate obligation.

Source: Aschbacher--Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), the local flag preceding (4.6), (4.6)--(4.8)
and section 5, printed pp.598--600, DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup MulAction
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Sporadic.Mathieu Sporadic.Mathieu.M22ValueBound.Concrete
open LocalGeometry LocalGeometry.LocalSubgroups

/-- Native geometric recognition of an order-5760 subgroup of M22. -/
theorem m22_card5760_eq_hexad (H : Subgroup M22) (hc : Nat.card H = 5760) :
    ∃ B ∈ m22Blocks, H = stabilizer M22 B := by
  have hU : ∃ U : Sylow 2 M22, (U : Subgroup M22) ≤ H := by
    let P : Sylow 2 H := Classical.choice inferInstance
    let A := P.toSubgroup.map H.subtype
    have hA : Nat.card A = 128 := by
      rw [card_map_of_injective H.subtype_injective, P.card_eq_multiplicity, hc]
      decide +kernel
    refine ⟨Sylow.ofCard A ?_, map_subtype_le _⟩
    rw [hA, m22_order]
    decide +kernel
  have hnt : ¬ IsPretransitive H (Fin 22) := by
    intro ht
    let := ht
    have hd : 22 ∣ Nat.card H := by
      have hi := (stabilizer H (0 : Fin 22)).index_dvd_card
      rw [index_stabilizer_of_transitive, Nat.card_fin] at hi
      exact hi
    rw [hc] at hd
    norm_num at hd
  rcases M22SolvableSylow.coverage_of_not_pretransitive H hU hnt with
    ⟨B,hB,hHB⟩ | ⟨S,hS,hHS⟩
  · exact ⟨B,hB,eq_of_le_of_card_ge hHB (by rw [m22Hexad_stabilizer_card hB,hc])⟩
  have hsc : Nat.card (stabilizer M22 S) = 1920 := by
    rcases Finset.card_eq_two.mp hS with ⟨x,y,hxy,rfl⟩
    obtain ⟨g,hg1,hg2⟩ := (is_two_pretransitive_iff.mp m22_isTwoPretransitive)
      (by decide : (1 : Fin 22) ≠ 2) hxy
    have hg : g • m22Pair12 = ({x,y} : Finset (Fin 22)) := by
      rw [m22Pair12,Finset.smul_finset_insert,Finset.smul_finset_singleton,←hg1,←hg2]
    exact (Nat.card_congr (stabilizerEquivStabilizer hg.symm).toEquiv).symm.trans m22PairStabilizer_card
  have hd := card_dvd_of_le hHS
  rw [hc,hsc] at hd
  norm_num at hd

/-- Recognize the literal hexad preserved by an order-11520 design subgroup. -/
theorem design_card11520_eq_hexad (R : Subgroup m22DesignAut) (hc : Nat.card R = 11520) :
    ∃ B ∈ m22Blocks, R = stabilizer m22DesignAut B := by
  let I := R.comap inclusion
  have hmap : I.map inclusion = R ⊓ M22ValueBound.Concrete.inner := by
    rw [map_comap_eq,inclusion_range,inf_comm]
  have hcI : Nat.card (M22ValueBound.Concrete.inner.subgroupOf R) = Nat.card I := by
    have e := (MulEquiv.subgroupCongr (inf_subgroupOf_left M22ValueBound.Concrete.inner R).symm).trans
      ((subgroupOfEquivOfLe (show R ⊓ M22ValueBound.Concrete.inner ≤ R from inf_le_left)).trans
        ((MulEquiv.subgroupCongr hmap.symm).trans
          (I.equivMapOfInjective inclusion inclusion_injective).symm))
    exact Nat.card_congr e.toEquiv
  have hinner : Nat.card (M22ValueBound.Concrete.inner : Subgroup m22DesignAut) = 443520 := by
    rw [←inclusion_range]
    exact (Nat.card_congr (MonoidHom.ofInjective M22ValueBound.Concrete.inclusion_injective).toEquiv).symm.trans m22_order
  have hnot : ¬ R ≤ M22ValueBound.Concrete.inner := by
    intro hle
    have hd := card_dvd_of_le hle
    rw [hc,hinner] at hd
    norm_num at hd
  have hle : (M22ValueBound.Concrete.inner.subgroupOf R).index ≤ 2 := by
    have hi := relIndex_le_of_le_right (H := M22ValueBound.Concrete.inner) (K := R) (L := ⊤) le_top
      (by simp [inner_index])
    rw [relIndex_top_right,inner_index] at hi
    exact hi
  have hne : (M22ValueBound.Concrete.inner.subgroupOf R).index ≠ 1 := fun hi => hnot (relIndex_eq_one.mp hi)
  have hpos : (M22ValueBound.Concrete.inner.subgroupOf R).index ≠ 0 := index_ne_zero_of_finite
  have hi : (M22ValueBound.Concrete.inner.subgroupOf R).index = 2 := by omega
  have hIc : Nat.card I = 5760 := by
    have he := (M22ValueBound.Concrete.inner.subgroupOf R).card_mul_index
    rw [hcI,hi,hc] at he
    omega
  obtain ⟨B,hB,hIB⟩ := m22_card5760_eq_hexad I hIc
  have hnorm : R ≤ normalizer (I.map inclusion : Set m22DesignAut) := by
    rw [hmap]
    exact (normal_subgroupOf_iff_le_normalizer (show R ⊓ M22ValueBound.Concrete.inner ≤ R from inf_le_left)).mp
      (by rw [inf_subgroupOf_left]; infer_instance)
  have hRB : R ≤ stabilizer m22DesignAut B := by
    apply hnorm.trans
    rw [hIB]
    exact M22SolvableSylow.normalizer_le_hexad_stabilizer hB _ le_rfl
      (m22HexadPointwiseKernel_le B)
  exact ⟨B,hB,eq_of_le_of_card_ge hRB (by rw [native_hex_card hB,hc])⟩

/-- The order-11520 automorphism subgroup is the stabilizer of a native hexad. -/
theorem aut_card11520_eq_hexad (A : Subgroup (MulAut M22)) (hc : Nat.card A = 11520) :
    ∃ B ∈ m22Blocks, A = designStabilizer B := by
  let R := A.map designAutEquiv.symm.toMonoidHom
  have hr : Nat.card R = 11520 := by
    rw [card_map_of_injective designAutEquiv.symm.injective,hc]
  obtain ⟨B,hB,he⟩ := design_card11520_eq_hexad R hr
  refine ⟨B,hB,?_⟩
  have hh := congrArg (map designAutEquiv.toMonoidHom) he
  rw [map_map] at hh
  have hid : designAutEquiv.toMonoidHom.comp designAutEquiv.symm.toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    exact designAutEquiv.apply_symm_apply x
  rw [hid,map_id] at hh
  exact hh

/-- Odd flag index forces the pair into the same native hexad. -/
theorem design_pair_subset_hexad_of_index {B A : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) (hA : A.card = 2)
    (hi : (stabilizer m22DesignAut A).relIndex (stabilizer m22DesignAut B) = 15) :
    A ⊆ B := by
  let H := stabilizer m22DesignAut B
  let J := (stabilizer m22DesignAut A).subgroupOf H
  let N := (M22OuterHexad.action hB).ker
  have hc : Nat.card N = 16 := by
    rw [←card_map_of_injective H.subtype_injective,M22OuterHexad.action_ker_map hB,
      card_map_of_injective inclusion_injective,m22HexadPointwiseKernel_card hB]
  have hcop : Nat.Coprime (Nat.card N) J.index := by
    change Nat.Coprime (Nat.card N) ((stabilizer m22DesignAut A).relIndex H)
    rw [hc,hi]
    decide
  have hd : J.relIndex N ∣ J.index := by
    rw [←relIndex_sup_of_normalizes N J le_normalizer_of_normal]
    exact relIndex_dvd_index_of_le le_sup_right
  have hn : N ≤ J := relIndex_eq_one.mp
    (Nat.eq_one_of_dvd_coprimes hcop (relIndex_dvd_card J N) hd)
  apply M22SolvableSylow.small_invariant_subset_hexad hB A (by omega)
  intro g hg
  have hm : inclusion g ∈ N.map H.subtype := by
    rw [M22OuterHexad.action_ker_map hB]
    exact mem_map_of_mem inclusion hg
  obtain ⟨n,hnn,he⟩ := hm
  have hh : n.val ∈ stabilizer m22DesignAut A := hn hnn
  change n.val = inclusion g at he
  rw [he] at hh
  exact hh

/-- The incidence test keeps the literal automorphism-group markings. -/
theorem aut_pair_subset_hexad_of_index {B A : Finset (Fin 22)}
    (hB : B ∈ m22Blocks) (hA : A.card = 2)
    (hi : (designStabilizer A).relIndex (designStabilizer B) = 15) : A ⊆ B := by
  apply design_pair_subset_hexad_of_index hB hA
  simpa only [designStabilizer,relIndex_map_map_of_injective _ _
    m22DesignAutToAut_injective] using hi

/-- Native pair recognition in the original automorphism-group marking. -/
theorem aut_card3840_eq_pair (A : Subgroup (MulAut M22)) (hc : Nat.card A = 3840) :
    ∃ B : Finset (Fin 22), B.card = 2 ∧ A = designStabilizer B := by
  let R := A.map designAutEquiv.symm.toMonoidHom
  have hr : Nat.card R = 3840 := by
    rw [card_map_of_injective designAutEquiv.symm.injective,hc]
  obtain ⟨B,hB,he⟩ := design_card3840_eq_pair R hr
  refine ⟨B,hB,?_⟩
  have hh := congrArg (map designAutEquiv.toMonoidHom) he
  rw [map_map] at hh
  have hid : designAutEquiv.toMonoidHom.comp designAutEquiv.symm.toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    exact designAutEquiv.apply_symm_apply x
  rw [hid,map_id] at hh
  exact hh

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The exact hexad preimage in the original plane group, with its cubic kernel. -/
theorem marked_pointPlane_hexad (h : IsTypeJ4 z)
    (e : CubicAutomorphismQuotient (centralizer z ⧸ core z)) (M : Subgroup G)
    (hM : Nat.card (M ⊓ centralizer z : Subgroup G) = 283115520) :
    ∃ B ∈ m22Blocks,
      (M.subgroupOf (centralizer z)).map (CubicLift.projection e) = designStabilizer B ∧
      M.subgroupOf (centralizer z) = (designStabilizer B).comap (CubicLift.projection e) := by
  obtain ⟨hc,hpre⟩ := marked_pointPlane_cubic_image h e M hM
  obtain ⟨B,hB,he⟩ := aut_card11520_eq_hexad _ hc
  exact ⟨B,hB,he,by rw [←he]; exact hpre.symm⟩

namespace ThreeSpaceData
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (CubicLift.subgroup e)} (d : ThreeSpaceData z e X)

/-- The full original cubic lift normalizes the same three-space. -/
theorem planeLine_contains_cubic (h : IsTypeJ4 z) :
    CubicLift.subgroup e ≤ (normalizer (d.space : Set G)).subgroupOf (centralizer z) := by
  rw [←core_sup_cubicSylow e h X]
  apply sup_le
  · intro q hq
    apply d.cores_normalize z
    · rw [d.generated]
      exact subset_closure (by simp)
    · intro he
      have hh := h.involution
      simp [he] at hh
    · exact mem_map_of_mem (centralizer z).subtype hq
  · intro q hq
    exact d.cubic_normalizes (mem_map_of_mem (centralizer z).subtype hq)

/-- Both image and preimage equations for the plane-line pair stabilizer. -/
theorem planeLine_pair (h : IsTypeJ4 z) :
    ∃ A : Finset (Fin 22), A.card = 2 ∧
      ((normalizer (d.space : Set G)).subgroupOf (centralizer z)).map (CubicLift.projection e) =
        designStabilizer A ∧
      (normalizer (d.space : Set G)).subgroupOf (centralizer z) =
        (designStabilizer A).comap (CubicLift.projection e) := by
  let L := (normalizer (d.space : Set G)).subgroupOf (centralizer z)
  have hn : CubicLift.subgroup e ≤ L := d.planeLine_contains_cubic h
  have hh := ((CubicLift.subgroup e).subgroupOf L).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hn).toEquiv,CubicLift.subgroup_card e h] at hh
  have hLc : Nat.card L = 94371840 := by
    rw [←card_map_of_injective (centralizer z).subtype_injective,subgroupOf_map_subtype,inf_comm]
    exact d.point_normalizer_card h
  change (3 * 2^13) * (CubicLift.projection e).ker.relIndex L = Nat.card L at hh
  rw [relIndex_ker,hLc] at hh
  have hc : Nat.card (L.map (CubicLift.projection e)) = 3840 := by omega
  obtain ⟨A,hA,he⟩ := aut_card3840_eq_pair _ hc
  exact ⟨A,hA,he,by rw [←he]; exact (comap_map_eq_self hn).symm⟩

/-- The original point-plane and plane-line subgroups are the inverse images
of an incident native pair-hexad flag under ONE original cubic projection. -/
theorem plane_flag (h : IsTypeJ4 z) (M : Subgroup G)
    (hM : Nat.card (M ⊓ centralizer z : Subgroup G) = 283115520)
    (hi : (normalizer (d.space : Set G)).relIndex (M ⊓ centralizer z) = 15) :
    ∃ (A B : Finset (Fin 22)), A.card = 2 ∧ B ∈ m22Blocks ∧ A ⊆ B ∧
      ((normalizer (d.space : Set G)).subgroupOf (centralizer z)).map (CubicLift.projection e) =
        designStabilizer A ∧
      (normalizer (d.space : Set G)).subgroupOf (centralizer z) =
        (designStabilizer A).comap (CubicLift.projection e) ∧
      (M.subgroupOf (centralizer z)).map (CubicLift.projection e) = designStabilizer B ∧
      M.subgroupOf (centralizer z) = (designStabilizer B).comap (CubicLift.projection e) := by
  obtain ⟨A,hA,heA,hpreA⟩ := d.planeLine_pair h
  obtain ⟨B,hB,heB,hpreB⟩ := marked_pointPlane_hexad h e M hM
  refine ⟨A,B,hA,hB,?_,heA,hpreA,heB,hpreB⟩
  apply aut_pair_subset_hexad_of_index hB hA
  have hnA : (CubicLift.projection e).ker ≤
      (normalizer (d.space : Set G)).subgroupOf (centralizer z) := d.planeLine_contains_cubic h
  have hnB : (CubicLift.projection e).ker ≤ M.subgroupOf (centralizer z) :=
    marked_pointPlane_contains_cubic h e M hM
  rw [←heA,←heB,relIndex_map_map,sup_of_le_left hnA,sup_of_le_left hnB]
  change ((normalizer (d.space : Set G)).comap (centralizer z).subtype).relIndex
    (M.subgroupOf (centralizer z)) = 15
  rw [relIndex_comap,subgroupOf_map_subtype]
  exact hi

end ThreeSpaceData

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
