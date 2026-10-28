module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualRecognition
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointPairs
public import CFSG.Quasithin.ChapterE.Section02.Structure.LinearThree.Placement
import all Theory.SpecificGroups.PSL3Even.UnipotentGeometry.MatrixModel
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The original PSL₃(4) normal-core overlap

The original full module has image of order at most four in the surviving
PSL₃(4) star quotient, by its literal long-root placement. Its intersection
with the original maximal normal core therefore has binary corank at most
two. If r(G,V)>2, centralizer control and the tensor Thompson fusion theorem
put the full normalizer of this overlap in M. Its stabilizer in H is exactly
H∩M.

The final application uses the actual point-normality input to obtain r>3
and feeds the existing old-residual A₅ recognition theorem. It retains the
unproved assertion that H normalizes this overlap in the PSL₃(4) branch.
Normality of the maximal core alone does not assert this, since V is only
known to be normalized by H∩M. No PSL₃(4) exclusion is claimed here.

Source: Aschbacher--Smith E.2.2 and E.2.7, printed pp.215--219;
9.2.7 and 9.4.1--3, printed pp.731,735--736.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3Even.UnipotentGeometry
open Matrix.PSL3Even.MinimalParabolicWitness
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- The literal full-module image lies in a field-four long-root group. -/
theorem old_residual_linear_three_star_image_card_le_four
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hK : (pResidual 2 H).IsCComponent)
    (hm : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax
        (T.subtype hH.1.1.2) hP) (pResidual 2 H)) 3 4) :
    let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
    Nat.card ((D.fullModule.subgroupOf H).map
      (QuotientGroup.mk' (ChapterB.minimalParabolicCore (T.subtype hH.1.1.2) hP))) ≤ 4 := by
  let S := T.subtype hH.1.1.2
  let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
  let J := ChapterB.minimalParabolicCore S hP
  let q := QuotientGroup.mk' J
  let S' := S.mapSurjective (QuotientGroup.mk'_surjective J)
  let V := D.fullModule.subgroupOf H
  let V' := V.map q
  let K := pResidual 2 H
  have hs : ¬ Group.IsSolvable H := by
    intro hh
    let := hh
    exact (Nat.not_le_of_gt hlarge) generationParameter_le_one_of_solvable
  have hVH : D.fullModule ≤ H := m.fullModule_le_sylow.trans hH.1.1.2
  let := m.fullModule_elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hVH
  let : IsElementaryAbelian 2 V' := IsElementaryAbelian.map q
  have hVS : V ≤ (S : Subgroup H) := comap_mono m.fullModule_le_sylow
  have hVN : (S : Subgroup H) ≤ normalizer (V : Set H) := by
    rw [← subgroupOf_normalizer_eq hVH]
    exact comap_mono ((le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule)
  have hV'S : V' ≤ (S' : Subgroup (H ⧸ J)) := map_mono hVS
  have hV'N : (S' : Subgroup (H ⧸ J)) ≤ normalizer (V' : Set (H ⧸ J)) :=
    (map_mono hVN).trans (V.le_normalizer_map q)
  have hi := ChapterE.Structure.source_normal_simple_image S hP hs K hK
    (pResidual_sup_sylow_eq_top S)
  let : IsSimpleGroup (K.map q) := hi.1
  let : (K.map q).Normal := hi.2.2.1
  have hstar := ChapterE.Structure.source_star_minimal_core_free S hP
  have hm' : ClassicalGroup.IsPSL (K.map q) 3 4 := hm
  obtain ⟨F,hfld,hfin,hF,⟨eF⟩⟩ := hm'
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by norm_num [← Nat.card_eq_fintype_card, hF])
  obtain ⟨g,_,_,hVroot⟩ := ChapterE.Structure.LinearThree.exists_longRoot_placement
    F (n := 2) (by decide) (by simpa using hF) (K.map q) eF S'
    hi.2.2.2 hstar.1 hstar.2 V' hV'S hV'N
  have hc := Subgroup.card_le_of_le hVroot
  rw [card_map_of_injective (modelEmbedding_injective F _ _), projectiveCenter,
    card_map_of_injective (projective_injective F), card_Z, hF] at hc
  exact hc

/-- The original ambient full-module/core overlap has binary corank at most two. -/
theorem old_residual_linear_three_overlap_corank_le_two
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hK : (pResidual 2 H).IsCComponent)
    (hm : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax
        (T.subtype hH.1.1.2) hP) (pResidual 2 H)) 3 4) :
    let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
    let J := ChapterB.minimalParabolicCore (T.subtype hH.1.1.2) hP
    subgroupCorank D.fullModule (D.fullModule ⊓ J.map H.subtype) ≤ 2 := by
  let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
  let J := ChapterB.minimalParabolicCore (T.subtype hH.1.1.2) hP
  have hVH : D.fullModule ≤ H := m.fullModule_le_sylow.trans hH.1.1.2
  have hi := relIndex_ker (K := D.fullModule.subgroupOf H) (QuotientGroup.mk' J)
  rw [QuotientGroup.ker_mk'] at hi
  have hb : J.relIndex (D.fullModule.subgroupOf H) ≤ 4 :=
    hi.le.trans (m.old_residual_linear_three_star_image_card_le_four hH hlarge hK hm)
  have hj : (J.map H.subtype).relIndex D.fullModule ≤ 4 := by
    rw [← map_subgroupOf_eq_of_le hVH,
      relIndex_map_map_of_injective _ _ H.subtype_injective]
    exact hb
  change Nat.log 2 ((D.fullModule ⊓ J.map H.subtype).relIndex D.fullModule) ≤ 2
  rw [inf_relIndex_left]
  exact (Nat.log_mono_right hj).trans (by decide : Nat.log 2 4 ≤ 2)

/-- The overlap has its full ambient normalizer in M as soon as r(G,V)>2. -/
theorem old_residual_linear_three_overlap_normalizer_le_of_globalR
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hK : (pResidual 2 H).IsCComponent)
    (hm : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax
        (T.subtype hH.1.1.2) hP) (pResidual 2 H)) 3 4)
    (hr : 2 < globalR D.fullModule) :
    let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
    let J := ChapterB.minimalParabolicCore (T.subtype hH.1.1.2) hP
    normalizer (D.fullModule ⊓ J.map H.subtype : Set G) ≤ D.maximalLocal := by
  apply m.tensor_normalizer_le_of_centralizer_le inf_le_left
  apply le_trans ?_ (source_fullModule_normalizer D).le
  apply centralizer_le_normalizer_of_corank_lt_globalR inf_le_left
  have hc := m.old_residual_linear_three_overlap_corank_le_two hH hlarge hK hm
  exact (show (subgroupCorank D.fullModule _ : ℕ∞) ≤ 2 by exact_mod_cast hc).trans_lt hr

/-- The actual H-stabilizer of the overlap is exactly the original maximal intersection. -/
theorem old_residual_linear_three_overlap_stabilizer_of_globalR
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hK : (pResidual 2 H).IsCComponent)
    (hm : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax
        (T.subtype hH.1.1.2) hP) (pResidual 2 H)) 3 4)
    (hr : 2 < globalR D.fullModule) :
    let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
    let J := ChapterB.minimalParabolicCore (T.subtype hH.1.1.2) hP
    H ⊓ normalizer (D.fullModule ⊓ J.map H.subtype : Set G) = H ⊓ D.maximalLocal := by
  let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
  let J := ChapterB.minimalParabolicCore (T.subtype hH.1.1.2) hP
  apply le_antisymm
  · exact inf_le_inf_left _ (m.old_residual_linear_three_overlap_normalizer_le_of_globalR
      hH hlarge hK hm hr)
  · apply le_inf inf_le_left
    have hn : H ≤ normalizer (J.map H.subtype : Set G) := by
      simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using
        J.le_normalizer_map H.subtype
    exact (le_inf (inf_le_right.trans D.maximalLocal_normalizes_fullModule)
      (inf_le_left.trans hn)).trans inf_normalizer_le_normalizer_inf

/-- Actual point normality and H-normality of the overlap discharge the precise PSL₃(4) premise. -/
theorem old_residual_a5_of_point_normality_of_overlap_normalized
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hpoint : ∀ v : D.fullModule, ((m.sectionData.coordinates v).toAdd).det ≠ 0 →
      centralizer ({(v : G)} : Set G) ≤ normalizer (m.tensorPointResidual v : Set G))
    (hoverlap : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      let J := ChapterB.minimalParabolicCore (T.subtype hH.1.1.2) hP
      (pResidual 2 H).IsCComponent → IsQuasisimple (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) →
        ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax
          (T.subtype hH.1.1.2) hP) (pResidual 2 H)) 3 4 →
        H ≤ normalizer (D.fullModule ⊓ J.map H.subtype : Set G)) :
    Nonempty (((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5)) := by
  apply m.old_residual_a5_of_no_linear_three_four hH hlarge
  dsimp only
  intro hc hq hl
  have hr : 2 < globalR D.fullModule :=
    lt_trans (by norm_num) (m.tensor_globalR_gt_three_of_point_normality hpoint)
  exact hH.1.2 ((hoverlap hc hq hl).trans
    (m.old_residual_linear_three_overlap_normalizer_le_of_globalR hH hlarge hc hl hr))

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
