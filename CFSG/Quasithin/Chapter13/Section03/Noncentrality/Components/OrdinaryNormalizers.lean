module

public import CFSG.Quasithin.Chapter13.Section03.SourceComponentRigidity
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.StarPlacement
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.OrbitSource
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryReductions

/-!
# Ordinary component normalizers in source 13.3.14(e–f)

The genuine 13.3.2 inputs make a faithful local component maximal: along a
local-component chain the Sylow group still normalizes the upper member, so
faithfulness ascends, and the mid-size quotient classification forces equality.
A C-component of the point normalizer is normal because its normalizer has
index at most two and already contains the prescribed Sylow two-subgroup.
The nonsolvable uniqueness theorem then supplies the actual maximal normalizer.
The point normalizer escapes M, which excludes L and the component from the
wrong maximal local subgroup. Finally ordinary parabolic generation excludes
the literal plane residual from the component normalizer.

Source: Aschbacher–Smith, Lemma 13.3.14(e–f), printed p.892. The genuine
faithful-local-component membership is supplied by Components.IntrinsicSource
and the actual selected-component application in OrdinaryComponents.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open SupercriticalSource Chapter1 Chapter1.Section02.Adequate
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]

/-- The two genuine 13.3.2 clauses promote a faithful local component to LStar. -/
theorem source1332_faithful_maximal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (h1332 : Source1332OneTwo T) {B : Subgroup G}
    (hf : B ∈ MainForward.faithfulLocalComponents T) : B ∈ LStar G T := by
  have hB := (mem_faithfulLocalComponents_iff T B).mp hf
  have hTB := (h1332 B hf).1
  refine ⟨hB.1, ?_⟩
  intro I hI hBI
  have hTI := local_chain_normalizes hB.1 hI hBI hTB
  have hn : (T : Subgroup G) ⊓ normalizer (B : Set G) =
      (T : Subgroup G) ⊓ normalizer (I : Set G) := by
    rw [inf_of_le_left hTB, inf_of_le_left hTI]
  have hfI := (faithful_chain_of_A410_of_normalizer_eq T (hG.evenCharacteristic T)
    ChapterA.Section04.SourceChains.adequate_source hf hI hBI hn).2
  exact (local_eq_of_midSize hI hB.1 hBI (h1332 I hfI).2).symm

variable {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d

/-- The actual point C-component is normal once its ambient image is faithful. -/
theorem ordinary_component_normal
    (h1332 : Source1332OneTwo T) (K : Subgroup H) (hK : K.IsCComponent)
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T) : K.Normal := by
  have hTH : (T : Subgroup G) ≤ H := d.first_normalizer ▸ d.line_stable
  have hP : P ≠ ⊥ := by intro he; have hh := d.line_card; simp [he] at hh
  have htwo : IsTwoLocal H := by
    rw [d.first_normalizer]
    exact ⟨P,hP,IsPGroup.of_card (n := 1) (by simpa using d.line_card),rfl⟩
  rcases Chapter1.Section02.component_normal_or_index_two_source
    (d.counterexample.qtke.twoLocal_sqtk htwo) hK with hn | hi
  · exact hn
  have hTN : (T : Subgroup G).subgroupOf H ≤ normalizer (K : Set H) := by
    have he : (K.map H.subtype).subgroupOf H = K :=
      comap_map_eq_self_of_injective H.subtype_injective K
    rw [←he, ←subgroupOf_normalizer_eq (map_subtype_le K)]
    exact comap_mono (h1332 _ hf).1
  have hd := index_dvd_of_le hTN
  change (normalizer (K : Set H)).index ∣ ((T : Subgroup G).subgroupOf H).index at hd
  rw [hi] at hd
  exact ((T.subtype hTH).not_dvd_index hd).elim

/-- Source reduction (e), including the literal uniqueness and exclusion clauses. -/
theorem ordinary_component_normalizer_conclusions
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : ¬IsMulCommutative (conjugateSpanBy V H))
    (h1332 : Source1332OneTwo T) (K : Subgroup H) (hK : K.IsCComponent)
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T) :
    K.map H.subtype ∈ LStar G T ∧
      H ≤ normalizer (K.map H.subtype : Set G) ∧
      IsMaximalTwoLocal (normalizer (K.map H.subtype : Set G)) ∧
      (∀ N : Subgroup G, IsMaximalTwoLocal N →
        K.map H.subtype ⊔ (T : Subgroup G) ≤ N →
          N = normalizer (K.map H.subtype : Set G)) ∧
      ¬ L ≤ normalizer (K.map H.subtype : Set G) ∧ ¬ K.map H.subtype ≤ M := by
  let B := K.map H.subtype
  have hB := source1332_faithful_maximal d.counterexample.qtke T h1332 hf
  have hTB := (h1332 B hf).1
  have hBn : (B.subgroupOf H).Normal := by
    have hn := ordinary_component_normal d h1332 K hK hf
    change ((K.map H.subtype).comap H.subtype).Normal
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  have hHN : H ≤ normalizer (B : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp hBn
  have hBuni := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    d.counterexample.qtke T hB
  have horb : componentOrbit B (T : Subgroup G) = B :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer B _ B le_rfl hTB)
      (le_componentOrbit B _)
  have hmax : IsMaximalTwoLocal (normalizer (B : Set G)) :=
    horb ▸ hBuni.normalizer_maximal
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → B ⊔ (T : Subgroup G) ≤ N →
      N = normalizer (B : Set G) := by
    intro N hN hBN
    have hu := hBuni.normalizer_unique N hN hBN
    change N = normalizer (componentOrbit B (T : Subgroup G) : Set G) at hu
    rwa [horb] at hu
  have hLuni := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h1221.simpleQTKE T h1221.maximal_faithful.1
  have hLorb : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L _ L le_rfl d.normalizes_L)
      (le_componentOrbit L _)
  have hMmax : IsMaximalTwoLocal M := by
    rw [d.local_normalizer, ←hLorb]
    exact hLuni.normalizer_maximal
  have hescape := ordinary_point_not_le_local d h1221 hV
  have hLn : ¬ L ≤ normalizer (B : Set G) := by
    intro hLN
    have he := hLuni.normalizer_unique _ hmax (sup_le hLN hTB)
    rw [hLorb, ←d.local_normalizer] at he
    exact hescape (hHN.trans_eq he)
  have hBM : ¬ B ≤ M := by
    intro hBM
    have hTM : (T : Subgroup G) ≤ M := d.local_normalizer ▸ d.normalizes_L
    exact hescape (hHN.trans_eq (huniq M hMmax (sup_le hBM hTM)).symm)
  exact ⟨hB,hHN,hmax,huniq,hLn,hBM⟩

private theorem ordinary_seed_local_le_point :
    L ⊓ normalizer (U : Set G) ≤ H := by
  rw [d.first_normalizer]
  intro x hx
  let g : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨x, mem_sup_left hx.1⟩
  apply (Section07.permutation_stabilizes_iff d P
    (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) g).mp
  have hs := (Section07.permutation_stabilizes_iff d U d.seed_le g).mpr hx.2
  rw [Section07.NaturalAction.seed_perpendicular d] at hs
  have hh := Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.stabilizer_le_orthogonal_stabilizer
    (Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.form.orthogonal
      (Section07.NaturalAction.image d P)) hs
  rwa [LinearMap.BilinForm.orthogonal_orthogonal
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.form_nondegenerate
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing.form_alt.isRefl] at hh

/-- The native ordinary plane actor cannot normalize the selected component. -/
theorem ordinary_plane_actor_not_normalizes_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : ¬IsMulCommutative (conjugateSpanBy V H))
    (h1332 : Source1332OneTwo T) (K : Subgroup H) (hK : K.IsCComponent)
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T) :
    ¬ Section05.PlaneGeometry.TwoBlocks.planeActor (L := L) (V₂ := E) ≤
      normalizer (K.map H.subtype : Set G) := by
  have h := ordinary_component_normalizer_conclusions d h1221 hV h1332 K hK hf
  intro hn
  apply h.2.2.2.2.1
  rw [Section05.PlaneGeometry.TwoBlocks.Ordinary.source_parabolic_generation d e]
  exact conjugateSpanBy_le hn ((ordinary_seed_local_le_point d).trans
    (h.2.1.trans (normalizer (K.map H.subtype : Set G)).le_normalizer))

/-- Source reduction (f) for the original residual of the plane normalizer. -/
theorem ordinary_reduction_f
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : ¬IsMulCommutative (conjugateSpanBy V H))
    (h1332 : Source1332OneTwo T) (K : Subgroup H) (hK : K.IsCComponent)
    (hf : K.map H.subtype ∈ MainForward.faithfulLocalComponents T) :
    ¬ sourceOne L T E ≤ normalizer (K.map H.subtype : Set G) := by
  have he : sourceOne L T E = Section05.PlaneGeometry.TwoBlocks.planeActor (L := L) (V₂ := E) :=
    Section08.TransvectionQuotients.FiveSeed.BarMarking.normalizer_residual_eq
      L E (T : Subgroup G) T.isPGroup' d.normalizes_L
  rw [he]
  exact ordinary_plane_actor_not_normalizes_component d e h1221 hV h1332 K hK hf

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
