module
public import CFSG.Quasithin.Chapter10.SourceA5PointLocalEmbedding
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedCenter

/-!
# Carrier data for the original quasisimple point component

The original fully moved elementary subgroup retains a nontrivial A₅ action
under a central quotient. Its image therefore has at least sixteen elements.
This is stronger than a cardinal bound on the core center: it gives an actual
elementary subgroup for the rank exclusions in the source embedding inspection.
The same containing component lies in the involution centralizer, so its simple
central quotient has the proved Theorem C catalogue.

Source: Aschbacher–Smith 10.2.9, printed pp.750–751, applying A.3.12.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- The literal moved subgroup stays elementary and large in every central image. -/
theorem source_a5_central_image_moved_elementary_card
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {H : Type*} [Group H] [Finite H] (f : L →* H) (hf : Function.Surjective f)
    (hker : f.ker ≤ center L) :
    IsElementaryAbelian 2 (((⁅D.fullModule,L⁆).subgroupOf L).map f) ∧
      16 ≤ Nat.card (((⁅D.fullModule,L⁆).subgroupOf L).map f) := by
  let W := ⁅D.fullModule,L⁆
  let A := W.subgroupOf L
  have hWL : W ≤ L := source_full_moved_le_component D
  have hmapA : A.map L.subtype = W := map_subgroupOf_eq_of_le hWL
  have hA : A.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_right _ _)
  let := hA
  let := source_original_full_moved_elementary D
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hWL
  let N := A.map f
  let : IsElementaryAbelian 2 N := IsElementaryAbelian.map f
  let : N.Normal := hA.map f hf
  have hmove : ⁅A,(⊤ : Subgroup L)⁆ = A := by
    apply map_injective L.subtype_injective
    rw [map_commutator,hmapA,←MonoidHom.range_eq_map,range_subtype]
    exact source_full_moved_eq_commutator D
  have hAne : A ≠ ⊥ := by
    intro h
    have hh := congrArg (map L.subtype) h
    rw [hmapA,Subgroup.map_bot] at hh
    exact source_full_moved_ne_bot D hh
  have hNmove : ⁅N,(⊤ : Subgroup H)⁆ = N := by
    rw [show (⊤ : Subgroup H) = (⊤ : Subgroup L).map f from
      (map_top_of_surjective _ hf).symm,←map_commutator,hmove]
  have hNnoncentral : ¬ N ≤ center H := by
    intro hn
    have hNzero : N = ⊥ := hNmove.symm.trans
      (commutator_top_right_eq_bot_iff_le_center.mpr hn)
    have hak : A ≤ f.ker := (map_eq_bot_iff A).mp hNzero
    exact hAne (hmove.symm.trans
      (commutator_top_right_eq_bot_iff_le_center.mpr (hak.trans hker)))
  let rho : L →* MulAut N := (MulAut.conjNormal : H →* MulAut N).comp f
  have hrho : rho ≠ 1 := by
    intro he
    apply hNnoncentral
    intro n hn
    apply mem_center_iff.mpr
    intro h
    obtain ⟨l,rfl⟩ := hf h
    have hh := congrArg (fun a : MulAut N => (a ⟨n,hn⟩ : H))
      (congrArg (fun r : L →* MulAut N => r l) he)
    change f l*n*(f l)⁻¹=n at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  exact ⟨inferInstance,
    alternatingGroup.FiveChiefDegree.sixteen_le_card_of_nontrivial_action
      D.faithful.1.2.1 e rho hrho (IsElementaryAbelian.isPGroup 2 N)⟩

/-- The literal original moved image is elementary of order at least sixteen. -/
theorem source_a5_containing_center_moved_elementary_card
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I : Subgroup G} (hLI : L ≤ I) :
    let E := ((⁅D.fullModule,L⁆).subgroupOf I).map (QuotientGroup.mk' (center I))
    IsElementaryAbelian 2 E ∧ 16 ≤ Nat.card E := by
  let A := L.subgroupOf I
  let q := QuotientGroup.mk' (center I)
  let B := A.map q
  let k : L ≃* A := (subgroupOfEquivOfLe hLI).symm
  let f : L →* B := (q.subgroupMap A).comp k.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective A).comp k.surjective
  have hk : f.ker ≤ center L := by
    intro l hl
    have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
    change q (inclusion hLI l) = 1 at hh
    have hc := (QuotientGroup.eq_one_iff (inclusion hLI l)).mp hh
    apply mem_center_iff.mpr
    intro m
    exact Subtype.ext (congrArg I.subtype (mem_center_iff.mp hc (inclusion hLI m)))
  obtain ⟨hN,h16⟩ := source_a5_central_image_moved_elementary_card D e f hf hk
  let N := ((⁅D.fullModule,L⁆).subgroupOf L).map f
  let := hN
  have hmap : N.map B.subtype =
      ((⁅D.fullModule,L⁆).subgroupOf I).map q := by
    rw [map_map]
    have hcomp : B.subtype.comp f = q.comp (inclusion hLI) := rfl
    rw [hcomp,←map_map]
    congr 1
    apply map_injective I.subtype_injective
    rw [map_map,subtype_comp_inclusion,
      map_subgroupOf_eq_of_le (source_full_moved_le_component D),
      map_subgroupOf_eq_of_le ((source_full_moved_le_component D).trans hLI)]
  rw [←hmap]
  refine ⟨IsElementaryAbelian.map B.subtype,?_⟩
  rwa [Nat.card_congr (N.equivMapOfInjective B.subtype B.subtype_injective).toEquiv] at h16

/-- The original local image contains an elementary subgroup of order at least sixteen. -/
theorem source_a5_containing_center_image_elementary
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {I : Subgroup G} (hLI : L ≤ I) :
    ∃ E : Subgroup (I ⧸ center I),
      E ≤ (L.subgroupOf I).map (QuotientGroup.mk' (center I)) ∧
      IsElementaryAbelian 2 E ∧ 16 ≤ Nat.card E := by
  refine ⟨((⁅D.fullModule,L⁆).subgroupOf I).map (QuotientGroup.mk' (center I)),
    map_mono (comap_mono (source_full_moved_le_component D)),?_⟩
  exact source_a5_containing_center_moved_elementary_card D e hLI

/-- The actual full point Sylow normalizes the same original moved image. -/
theorem source_a5_point_center_moved_normalized
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    {I : Subgroup G} (hLI : L ≤ I) (S : Sylow 2 I)
    (hSm : (S : Subgroup I).map I.subtype =
      ((T : Subgroup G) ⊓ centralizer ({v} : Set G)) ⊓ I) :
    (S.mapSurjective (QuotientGroup.mk'_surjective (center I)) : Subgroup (I ⧸ center I)) ≤
      normalizer (((⁅D.fullModule,L⁆).subgroupOf I).map
        (QuotientGroup.mk' (center I)) : Set (I ⧸ center I)) := by
  have hRL : (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤
      normalizer (L : Set G) :=
    (inf_le_inf (le_normalizer_componentOrbit L T) le_rfl).trans
      (source_nonnormal_element_centralizer_stabilizes D hn hvL hv0)
  have hRW : (T : Subgroup G) ⊓ centralizer ({v} : Set G) ≤
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hRL hg),
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
        (le_normalizer_componentOrbit L T hg.1))]
  have hSW : (S : Subgroup I) ≤ normalizer ((⁅D.fullModule,L⁆).subgroupOf I : Set I) := by
    rw [←subgroupOf_normalizer_eq ((source_full_moved_le_component D).trans hLI)]
    intro s hs
    apply hRW
    have hh : (s : G) ∈ (S : Subgroup I).map I.subtype := mem_map_of_mem I.subtype hs
    rw [hSm] at hh
    exact hh.1
  exact (map_mono hSW).trans (le_normalizer_map (QuotientGroup.mk' (center I)))

/-- The original point component supplies the actual simple quotient catalogue. -/
theorem source_a5_point_center_quotient_theoremC_model
    (t : G) {v : G}
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    {I : Subgroup G} [IsQuasisimple I] (hIX : I ≤ centralizer ({v} : Set G)) :
    ChapterA.Section02.IsTheoremCModel (I ⧸ center I) := by
  let := source_original_full_moved_elementary D
  let U := (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  have hv2 : orderOf v = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian v hv) hvne
  have hI : IsSQTK KnownSimple.IsKnownSimple I :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hIX)).mp
      ((D.simpleQTKE.involution_centralizer_sqtk hv2).subgroup _)
  exact ChapterA.Section03.SourceEmbeddings.quasisimple_center_quotient_theoremC_model hI

end CFSG.Quasithin.Chapter10
