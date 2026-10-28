module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryFullAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.FullMarkedImages
public import Theory.GroupTheory.Commutator.ConjugateOrbitCentralizer

/-!
# The original seed-fixing Borel marking

The actual kernel of the Borel action on L/O₂(L) fixes the flag point.
Its commutators with L lie in O₂(L), which fixes V, so it fixes the whole
L-orbit of that point, namely V. This proves that the original B_C fixes
the seed without assuming a module decomposition.

In the exchanged field-four branch, B_C has a nontrivial image in the
paired Borel: otherwise the cubic image of L₁ would cover a torus of order
nine. This image is normal, two-perfect and exchange-invariant, hence its
first projection is the whole factor Borel. Transport through the original
star map gives L₁* ≤ B_C* K₂*, retaining the surviving two-cores. The source
application constructs this marking from the original nonnormal component.

Source: Aschbacher–Smith, proof of 14.7.32, printed pp.1056–1057,
refs/quasithin.pdf. This supplies the actual fixing and projection inputs
to the factor-module exclusion; it does not assert orthogonal recognition.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components Swapped Swapped.LinearTwo
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Fixation of the original flag point extends to its full L-orbit V. -/
theorem binaryBorelCentralResidual_centralizes_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (B : Subgroup G) (hBM : B ≤ normalizer (L : Set G)) (hBH : B ≤ F.H) :
    binaryBorelCentralResidual L B hBM ≤ centralizer (V : Set G) := by
  let C := binaryBorelCentralResidual L B hBM
  have hCB : C ≤ B := map_subtype_le _
  have hCM := hCB.trans hBM
  have hc : ⁅L,C⁆ ≤ L.pCoreIn 2 := by
    apply commutator_le_of_normalizerQuotientAction_eq_one L C (pCore 2 L) hCM
    rintro ⟨x,hx⟩
    obtain ⟨b,⟨c,hc,rfl⟩,rfl⟩ := hx
    exact c.property
  have hCP : C ≤ centralizer (F.Vi 1 : Set G) :=
    (hCB.trans hBH).trans (normalizer_le_centralizer_of_card_two _ (by
      simpa using F.card 1 (by decide)))
  have hspan : componentOrbit (F.Vi 1) L = V := by
    change (⨆ l : L, (F.Vi 1).map (MulAut.conj (l : G)).toMonoidHom) = V
    rw [←conjugateSpanBy_eq_iSup_conj]
    apply le_antisymm (conjugateSpanBy_le (F.le_seed 1) h.chosen.normalizes)
    intro v hv
    by_cases he : v = 1
    · exact he ▸ (conjugateSpanBy (F.Vi 1) L).one_mem
    obtain ⟨z,hz,hpoint⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
    have hzP : z ∈ F.Vi 1 := hpoint ▸ mem_zpowers z
    obtain ⟨l,hl,rfl⟩ := h.vector_transitive (F.le_seed 1 hzP) hv hz he
    exact subset_closure ⟨l,hl,z,hzP,rfl⟩
  have hQ : L.pCoreIn 2 ≤ centralizer (componentOrbit (F.Vi 1) L : Set G) := by
    rw [hspan,←h.centralizer_L]
    exact inf_le_right
  simpa only [hspan] using conjugateOrbit_centralizes_of_commutator_centralizes
    L C (F.Vi 1) (L.pCoreIn 2) hc hQ hCP


private theorem centralResidual_perfect (L B : Subgroup G)
    (hBM : B ≤ normalizer (L : Set G)) :
    IsPPerfect 2 (binaryBorelCentralResidual L B hBM) := by
  let R := (pResidual 2 (binaryBorelAction L B hBM).ker).map
    (binaryBorelAction L B hBM).ker.subtype
  exact (isPPerfect_embedded_pResidual 2 (binaryBorelAction L B hBM).ker).of_surjective
    (B.subtype.subgroupMap R) (B.subtype.subgroupMap_surjective R)

private theorem point_borel_factor_cosets
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I K : Subgroup G) (hTI : (T : Subgroup G) ≤ I)
    (t : G) (ht : t ∈ T) (htn : t ∉ normalizer (K : Set G))
    (hi : (normalizer (K.subgroupOf I : Set I)).index = 2)
    (hNI : K ⊔ K.conjBy t ≤ I)
    (e : Chapter13.Section08.Source.starImage I (K ⊔ K.conjBy t) ≃*
      Chapter13.Section08.Source.starImage I K × Chapter13.Section08.Source.starImage I K)
    (he : ∀ a b, (e.symm (a,b) : Chapter13.Section08.Source.Hstar I) =
      (a : Chapter13.Section08.Source.Hstar I) *
        (QuotientGroup.mk' (pCore 2 I) ⟨t,hTI ht⟩ * b *
          (QuotientGroup.mk' (pCore 2 I) ⟨t,hTI ht⟩)⁻¹))
    (S : Sylow 2 (Chapter13.Section08.Source.starImage I (K ⊔ K.conjBy t)))
    (hm : ClassicalGroup.IsPSL (Chapter13.Section08.Source.starImage I K) 2 4)
    (hBM : SourceTorus.chosenLift I (K ⊔ K.conjBy t) hNI S ≤ normalizer (L : Set G))
    (hAB : F.Li L 1 ≤ (pResidual 2 (SourceTorus.chosenLift I (K ⊔ K.conjBy t) hNI S)).map
      (SourceTorus.chosenLift I (K ⊔ K.conjBy t) hNI S).subtype)
    (hBA : SourceTorus.chosenLift I (K ⊔ K.conjBy t) hNI S ≤ normalizer (F.Li L 1 : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (SourceTorus.chosenLift I (K ⊔ K.conjBy t) hNI S : Set G)) :
    let B₀ := SourceTorus.chosenLift I (K ⊔ K.conjBy t) hNI S
    let B := (pResidual 2 B₀).map B₀.subtype
    let C := binaryBorelCentralResidual L B ((map_subtype_le _).trans hBM)
    Chapter13.Section08.Source.starImage I (F.Li L 1) ≤
      Chapter13.Section08.Source.starImage I C ⊔ Chapter13.Section08.Source.starImage I (K.conjBy t) := by
  let N := K ⊔ K.conjBy t
  let B₀ := SourceTorus.chosenLift I N hNI S
  let B := (pResidual 2 B₀).map B₀.subtype
  have hBB : B ≤ B₀ := map_subtype_le _
  let C := binaryBorelCentralResidual L B (hBB.trans hBM)
  have hCB : C ≤ B₀ := (map_subtype_le _).trans hBB
  have hLB : F.Li L 1 ≤ B₀ := hAB.trans hBB
  have hnC : B₀ ≤ normalizer (C : Set G) :=
    (le_inf (B₀.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B₀ (pResidual 2 B₀))) hBM).trans
      (binaryBorelCentralResidual_normalized L B (hBB.trans hBM))
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf (hTB.trans (normalizer_le_normalizer_characteristic_image B₀ (pResidual 2 B₀)))
      (h.sylow_normalizes structural)).trans
      (binaryBorelCentralResidual_normalized L B (hBB.trans hBM))
  let S' := SourceTorus.chosenSylow I N e S
  let f := SourceTorus.toBinary I N hNI e S
  let D := (C.subgroupOf B₀).map f
  let R := SourceActions.CommonTorus I N e S
  let q := SourceTorus.toCommonTori I N hNI e S (n := 2) (by decide) hm
  have hk : IsPGroup 2 q.ker := by rw [SourceTorus.toCommonTori_ker]; exact pCore_isPGroup
  have ho := SourceActions.commonTori_odd I N e S (n := 2) (by decide) hm
  let α := SourceTorus.normalizerAction I N hNI e S (n := 2) (by decide) hm ⟨1,one_mem _⟩
  have hsup := (point_borel_torus_supplement h structural B₀ hBM hAB hBA q
    (SourceTorus.toCommonTori_surjective I N hNI e S (n := 2) (by decide) hm)
    hk ho 1 (one_mem L) (one_mem _) α
    (SourceTorus.normalizerAction_toCommonTori I N hNI e S (n := 2) (by decide) hm _)).1
  have hne : D ≠ ⊥ := by
    intro hz
    have hz' : SourceActions.Markings.image B₀ C q = ⊥ := by
      change ((C.subgroupOf B₀).map ((SourceActions.binaryToCommon I N e S (n := 2) (by decide) hm).comp f)) = ⊥
      rw [←map_map]
      change D.map _ = ⊥
      rw [hz,Subgroup.map_bot]
    change SourceActions.Markings.image B₀ (F.Li L 1) q ⊔ SourceActions.Markings.image B₀ C q = ⊤ at hsup
    rw [hz',sup_bot_eq] at hsup
    have hc := SourceActions.Markings.image_card B₀ (F.Li L 1) hLB q hk ho
    rw [pointResidual_core_quotient_card h structural,hsup,card_top] at hc
    have hR : Nat.card R = 3 := BinaryBorel.torus_four_card hm _
    rw [Nat.card_prod,hR] at hc
    norm_num at hc
  let : (C.subgroupOf B₀).Normal := normal_subgroupOf_of_le_normalizer hnC
  let : D.Normal := (inferInstance : (C.subgroupOf B₀).Normal).map f
    (SourceTorus.toBinary_surjective I N hNI e S)
  have hp : IsPPerfect 2 D := by
    have hpC := (centralResidual_perfect L B (hBB.trans hBM)).of_surjective
      (subgroupOfEquivOfLe hCB).symm.toMonoidHom (subgroupOfEquivOfLe hCB).symm.surjective
    exact hpC.of_surjective (f.subgroupMap _) (f.subgroupMap_surjective _)
  have hnN := SourceActions.normalizes_orbit I K (le_sup_left.trans hNI) hi (hTI ht) htn
  let τ := SourceActions.binaryAction I N hNI e S (hTI ht) (hnN (hTI ht)) (hTB ht)
  have hτ := (SourceActions.binary_moving_exchanges I K (hTI ht) hNI hi htn e he S
    (hnN (hTI ht)) (hTB ht)).2
  have hD := SourceActions.binary_image_invariant I N hNI e S C
    (hTI ht) (hnN (hTI ht)) (hTB ht) (hTC ht)
  have him := BorelProjections.first_image_eq_top hm S' τ hτ D hD hne hp
  have hmaps : (((F.Li L 1).subgroupOf B₀).map f).map (BorelProjections.firstProjection S') ≤
      D.map (BorelProjections.firstProjection S') := by rw [him]; exact le_top
  have hamb := map_mono (f := (BinaryBorel.borel (BinaryBorel.firstSylow S')).subtype) hmaps
  have hcomp : (BinaryBorel.borel (BinaryBorel.firstSylow S')).subtype.comp
      ((BorelProjections.firstProjection S').comp f) =
      (MonoidHom.fst _ _).comp ((BinaryBorel.borel S').subtype.comp f) := by
    apply MonoidHom.ext
    intro x
    exact BorelProjections.firstProjection_apply S' (f x)
  have hamb' : ((((F.Li L 1).subgroupOf B₀).map f).map (BinaryBorel.borel S').subtype).map
      (MonoidHom.fst _ _) ≤
      (((C.subgroupOf B₀).map f).map (BinaryBorel.borel S').subtype).map (MonoidHom.fst _ _) := by
    simpa only [D,Subgroup.map_map,hcomp] using hamb
  rw [SourceConclusion.binary_image_eq_star_image I N hNI e S _ hLB,
    SourceConclusion.binary_image_eq_star_image I N hNI e S _ hCB,map_map,map_map] at hamb'
  let π := SourceConclusion.factorProjection I N e
  have hker := SourceConclusion.factorProjection_kernel I K T hTI ht hNI e he
  have hle : (Chapter13.Section08.Source.starImage I (F.Li L 1)).subgroupOf
      (Chapter13.Section08.Source.starImage I N) ≤
      (Chapter13.Section08.Source.starImage I C).subgroupOf (Chapter13.Section08.Source.starImage I N) ⊔
        (Chapter13.Section08.Source.starImage I (K.conjBy t)).subgroupOf (Chapter13.Section08.Source.starImage I N) := by
    rw [←hker,←comap_map_eq]
    exact (map_le_iff_le_comap).mp hamb'
  have hCN : C ≤ N := hCB.trans (borelLift_le I N hNI _)
  have hLN : F.Li L 1 ≤ N := hLB.trans (borelLift_le I N hNI _)
  have hPN : Chapter13.Section08.Source.starImage I (F.Li L 1) ≤
      Chapter13.Section08.Source.starImage I N := map_mono (subgroupOf_mono I hLN)
  have hDN : Chapter13.Section08.Source.starImage I C ≤
      Chapter13.Section08.Source.starImage I N := map_mono (subgroupOf_mono I hCN)
  have hKN : Chapter13.Section08.Source.starImage I (K.conjBy t) ≤
      Chapter13.Section08.Source.starImage I N := map_mono (subgroupOf_mono I le_sup_right)
  have hmle := map_mono (f := (Chapter13.Section08.Source.starImage I N).subtype) hle
  rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le hPN,
    map_subgroupOf_eq_of_le hDN,map_subgroupOf_eq_of_le hKN] at hmle

/-- The actual nonnormal branch supplies a seed-fixing subgroup whose first
component cosets cover the original point group. All groups and quotient
maps belong to the original full point normalizer. -/
theorem local_nonnormal_component_seed_cosets
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ∃ t : G, t ∈ T ∧ t ∉ normalizer (K : Set G) ∧
      ∃ Z : Subgroup G,
        Z ≤ conjugateSpanBy K (T : Subgroup G) ∧
        Z ≤ centralizer (V : Set G) ∧
        Chapter13.Section08.Source.starImage F.H (F.Li L 1) ≤
          Chapter13.Section08.Source.starImage F.H Z ⊔
            Chapter13.Section08.Source.starImage F.H (K.conjBy t) := by
  have hEq := (local_nonnormal_component_eq_full_point d h hab structural previous faithful earlier
    I K hI hKI hK hnormal).2.1
  subst I
  have hTI := F.sylow_le_of_mem_Hz hI
  have hm := local_nonnormal_component_field_four d h hab structural previous faithful earlier
    F.H K hI hKI hK hnormal
  have hi := ((Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
    (local_star_sqtk h F.H hI) hK).resolve_left hnormal).1
  have hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K := by
    intro he
    exact hnormal (normal_of_sylow_span_eq F.H K T hKI hTI (Or.inr hi) he)
  obtain ⟨t,ht,htn,hNI,e,S,horbit,hcoord,hres,hS,him,hsol,hLB,hBM,hnB,hBN,hLres,
    heven,hrank,hP,hfst,hsnd⟩ :=
    local_binary_borel d h hab structural previous faithful earlier F.H K hI hKI hK
      (n := 2) (by decide) hm hmoving
  let B₀ := SourceTorus.chosenLift F.H (K ⊔ K.conjBy t) hNI S
  let B := (pResidual 2 B₀).map B₀.subtype
  have hBB : B ≤ B₀ := map_subtype_le _
  let Z := binaryBorelCentralResidual L B (hBB.trans hBM)
  have hZB : Z ≤ B₀ := (map_subtype_le _).trans hBB
  have hB₀N := borelLift_le F.H (K ⊔ K.conjBy t) hNI (SourceTorus.chosenStarBorel F.H _ S)
  refine ⟨t,ht,htn,Z,?_,?_,?_⟩
  · rw [horbit]
    exact hZB.trans hB₀N
  · exact binaryBorelCentralResidual_centralizes_seed h B (hBB.trans hBM)
      (hBB.trans (hB₀N.trans hNI))
  · exact point_borel_factor_cosets h structural F.H K hTI t ht htn hi hNI e hcoord S hm
      hBM hLres hBN (le_sup_right.trans hnB)


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
