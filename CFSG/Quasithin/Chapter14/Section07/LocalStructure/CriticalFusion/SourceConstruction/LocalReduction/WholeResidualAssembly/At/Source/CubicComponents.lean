module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCubicGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.NaturalRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.ChiefCubicGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicLocalStructure
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Subnormal
public import Theory.GroupTheory.NormalClosureCentralizerCore
public import Theory.GroupTheory.ReducedNormal.CentralSeedOvergroup
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicActionQuotient
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicComponents
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Centralizing
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Contract
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension
public import Theory.GroupTheory.CComponent.RadicalKernel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentReduction
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicLinearAction
public import Theory.SpecificGroups.AlternatingFiveSolvableSylow
public import Theory.SpecificGroups.PSL3Two.Automorphisms.SylowStabilizer
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicNaturalModule
public import Theory.Representation.ConjugatePointNatural
public import Theory.SpecificGroups.PSL3Two.NonSolvable
public import Theory.Representation.SpecialLinearThreeTransitivity
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicFaithfulCompletion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicSolvability
public import Theory.GroupAction.RankTwoCosetGeometry.CommutingSeeds
public import Theory.GroupTheory.ConjugatePairInternalLift

/-!
# Guarded cubic components

This unit collects the indicated original source arguments at the same G,T.
Each constituent overview records its proof and source; the universal exports
remain unchanged. The larger unit avoids repeated loading of the common source
imports. Public mathematical statements and literal subgroup maps are retained.
-/

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The action kernel of the original cubic completion

For D = ⟨L₂,Y,T⟩ and W = ⟨V₁^D⟩, the Sylow-central seed makes the
literal conjugation quotient D/C_D(W) two-reduced. In the normal-point
branch, the plane-span obstruction shows that Y's image does not normalize
L₂'s image under the actual quotient map.

Both local residuals act nontrivially on W. The Goldschmidt intersection
lemma then gives C_T(W) = O₂(D). The application constructs this geometry
from the original order-four chief interval, retaining its escaping cubic,
normalization of L₁, and exact star kernel.

These are the initial geometric and kernel steps of the containment
argument. Solvability of D and the later exclusions proving 14.5.3(2)
remain necessary; the small interval is not excluded here.

Source: Aschbacher–Smith, 14.5.6 and 14.5.7(2--3), printed p.1014,
B.2.14, printed p.78, and 14.7.20(2), printed p.1049, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual point span has two-reduced conjugation action in the generated
local group, as required by source 14.5.7(3). -/
theorem cubic_generated_span_reduced
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    Theory.GroupTheory.IsPReduced 2 ((conjugateSpanBy (F.Vi 1) D).subgroupOf D) := by
  let := h.chosen.elementary
  let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
  have hh := (cubic_generated_local_structure h hab structural previous Y hYH he).1
  apply Theory.GroupTheory.reduced_conjugateSpan_of_sylow_central T
  · exact le_sup_right.trans le_sup_right
  · exact (F.le_seed 1).trans h.chosen.le_sylow
  · exact le_centralizer_iff.mp ((F.invariant 1).trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))))
  · exact (Theory.GroupTheory.inf_centralizer_pCoreIn_le_iff 2 _).mp hh

/-- In the literal action quotient D/C_D(W), the escaping cubic does not
normalize the original plane residual image. This is source 14.5.6 in the
normal-point branch, with the actual quotient map. -/
theorem cubic_generated_action_normalizer_obstruction_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hout : ¬ Y ≤ normalizer (L : Set G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
    ¬ (Y.subgroupOf D).map q ≤ normalizer (((F.Li L 2).subgroupOf D).map q : Set _) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  have hYD : Y ≤ D := le_sup_left.trans le_sup_right
  have hXD : F.Li L 2 ≤ D := by
    change F.Li L 2 ≤ F.P L ⊔ (Y ⊔ (T : Subgroup G))
    rw [plane_parabolic_eq_join h structural]
    exact le_sup_left.trans le_sup_left
  have hWD : W ≤ D := conjugateSpanBy_le_self
    ((F.le_seed 1).trans (h.chosen.le_sylow.trans (le_sup_right.trans le_sup_right)))
  have hC : C.map D.subtype = D ⊓ centralizer (W : Set G) := by
    rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hWD]
  change ¬ (Y.subgroupOf D).map q ≤ normalizer (((F.Li L 2).subgroupOf D).map q : Set _)
  intro him
  have hpre := map_le_iff_le_comap.mp him
  rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective C),
    comap_map_eq,QuotientGroup.ker_mk'] at hpre
  have hh := (map_mono (f := D.subtype) hpre).trans (le_normalizer_map D.subtype)
  rw [map_subgroupOf_eq_of_le hYD,Subgroup.map_sup,map_subgroupOf_eq_of_le hXD,hC] at hh
  exact cubic_plane_normalizer_obstruction_of_normalizes_point h structural Y hYH hYL hout hh

/-- The original full point-normality interface. -/
theorem cubic_generated_action_normalizer_obstruction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hout : ¬ Y ≤ normalizer (L : Set G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
    ¬ (Y.subgroupOf D).map q ≤ normalizer (((F.Li L 2).subgroupOf D).map q : Set _) := by
  apply cubic_generated_action_normalizer_obstruction_of_normalizes_point h structural Y hYH _ hout
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The Sylow centralizer of the literal point span is the generated group's
own two-core. This is the kernel equality in source 14.5.7(2). -/
theorem cubic_generated_sylow_centralizer_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    (T : Subgroup G) ⊓ centralizer (W : Set G) = D.pCoreIn 2 := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let A := (F.P L).subgroupOf D
  let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
  let C := centralizer (W.subgroupOf D : Set D)
  have hPD : F.P L ≤ D := le_sup_left
  have hBD : Y ⊔ (T : Subgroup G) ≤ D := le_sup_right
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans hBD
  have hYD : Y ≤ D := le_sup_left.trans hBD
  have hXD : F.Li L 2 ≤ D := by
    apply le_trans _ hPD
    rw [plane_parabolic_eq_join h structural]
    exact le_sup_left
  have hZD : F.Vi 1 ≤ D := (F.le_seed 1).trans (h.chosen.le_sylow.trans hTD)
  have hWD : W ≤ D := conjugateSpanBy_le_self hZD
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  have hC : C.map D.subtype = D ⊓ centralizer (W : Set G) := by
    rw [map_centralizer_subtype,map_subgroupOf_eq_of_le hWD]
  have hRA : ((pResidual 2 A).map A.subtype).map D.subtype = F.Li L 2 := by
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hPD,
      plane_parabolic_residual h structural]
  have hRB : ((pResidual 2 B).map B.subtype).map D.subtype = Y := by
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hBD]
    exact embedded_pResidual_join_pGroup Y _ hYp T.isPGroup' hYT
  have hXA : ¬ (pResidual 2 A).map A.subtype ≤ C := by
    intro hle
    have hXC : F.Li L 2 ≤ centralizer (W : Set G) := by
      have hh := map_mono (f := D.subtype) hle
      rw [hRA,hC] at hh
      exact hh.trans inf_le_right
    have hXpoint : F.Li L 2 ≤ normalizer (F.Vi 1 : Set G) :=
      (hXC.trans (centralizer_le (le_conjugateSpanBy _ _))).trans
        (Subgroup.centralizer_le_normalizer _)
    have heq : F.Vi 2 ≤ F.Vi 1 := by
      rw [←plane_eq_point_residual_span h structural]
      exact conjugateSpanBy_le le_rfl hXpoint
    have hc := card_le_of_le heq
    rw [F.card 2 (by decide),F.card 1 (by decide)] at hc
    norm_num at hc
  have hYB : ¬ (pResidual 2 B).map B.subtype ≤ C := by
    intro hle
    have hh := map_mono (f := D.subtype) hle
    rw [hRB,hC] at hh
    apply cubic_plane_normalizer_obstruction_of_normalizes_point h structural Y hYH hYL hout
    exact hh.trans (le_sup_right.trans (F.Li L 2 ⊔ (D ⊓ centralizer (W : Set G))).le_normalizer)
  have ht := cubic_goldschmidt_triple h structural Y hYH he
  have hAC : A ⊓ C ≤ (pCore 2 A).map A.subtype :=
    (ht.left_subnormal_core_iff_not_residual_le C (Normal.isSubnormal inferInstance)).mpr hXA
  have hBC : B ⊓ C ≤ (pCore 2 B).map B.subtype :=
    (ht.right_subnormal_core_iff_not_residual_le C (Normal.isSubnormal inferInstance)).mpr hYB
  have hinter : A ⊓ B = (T : Subgroup G).subgroupOf D := by
    have hle : A ⊓ B ≤ (T : Subgroup G).subgroupOf D := by
      intro x hx
      have hh : (x : G) ∈ F.P L ⊓ F.H := ⟨hx.1,(sup_le hYH (F.invariant 1)) hx.2⟩
      rwa [plane_parabolic_inf_point h structural] at hh
    apply le_antisymm hle
    intro x hx
    exact ⟨F.binary_sylow_le_P L hx,(le_sup_right : (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G)) hx⟩
  have hlow := ht.normal_intersection_le_twoCore C hAC hBC
  rw [hinter] at hlow
  have hQC := (cubic_generated_local_structure h hab structural previous Y hYH he).2.2.2.2
  have hQT : D.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow D (T.subtype hTD)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTD] using hh
  change (T : Subgroup G) ⊓ centralizer (W : Set G) = D.pCoreIn 2
  apply le_antisymm
  · intro x hx
    have hc : (⟨x,hTD hx.1⟩ : D) ∈ C := by
      intro w hw
      exact Subtype.ext (hx.2 w hw)
    exact mem_map_of_mem D.subtype (hlow ⟨hx.1,hc⟩)
  · exact le_inf hQT (le_centralizer_iff.mp hQC)

/-- The original full point-normality interface. -/
theorem cubic_generated_sylow_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    (T : Subgroup G) ⊓ centralizer (W : Set G) = D.pCoreIn 2 := by
  apply cubic_generated_sylow_centralizer_of_normalizes_point h hab structural previous Y hYH _ hYp hYT hout he
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement in
/-- The actual order-four interval supplies the source 14.5.5--7 geometry,
with the same escaping cubic, star kernel, quotient, and point span. -/
theorem extraspecial_four_interval_cubic_geometry
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 ∧
      Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      let W := conjugateSpanBy (F.Vi 1) D
      ChapterF.IsGoldschmidtTriple ((F.P L).subgroupOf D)
        ((Y ⊔ (T : Subgroup G)).subgroupOf D) ∧
      pCore 2 D ≠ ⊥ ∧ D ∈ Chapter1.He G ∧ IsSQTK KnownSimple.IsKnownSimple D ∧
      IsElementaryAbelian 2 W ∧ W ≤ D.pCoreIn 2 ∧
      W ≤ centralizer (D.pCoreIn 2 : Set G) ∧
      Theory.GroupTheory.IsPReduced 2 (W.subgroupOf D) ∧
      (T : Subgroup G) ⊓ centralizer (W : Set G) = D.pCoreIn 2 ∧
      ¬ Y ≤ normalizer ((F.Li L 2 ⊔ (D ⊓ centralizer (W : Set G)) : Subgroup G) : Set G) ∧
      letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy _ _)
      let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
      ¬ (Y.subgroupOf D).map q ≤ normalizer (((F.Li L 2).subgroupOf D).map q : Set _) := by
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he⟩ :=
    extraspecial_four_interval_escaping_symmetricThree h hab structural previous hex hcard hexp
      N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨hHe,hSQ,hW,hWQ,hWC⟩ := cubic_generated_local_structure h hab structural previous Y hYH he
  exact ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,
    cubic_goldschmidt_triple h structural Y hYH he,
    cubic_generated_core_ne_bot h hab structural previous Y hYH he,
    hHe,hSQ,hW,hWQ,hWC,
    cubic_generated_span_reduced h hab structural previous Y hYH he,
    cubic_generated_sylow_centralizer h hab structural previous hn Y hYH hYp hYT hout he,
    cubic_plane_normalizer_obstruction h structural hn Y hYH hout,
    cubic_generated_action_normalizer_obstruction h structural hn Y hYH hout⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The faithful cubic action quotient and its solvable kernel

For D = ⟨L₂,Y,T⟩ and W = ⟨V₁^D⟩, the nonnormalizing residual images
force each original vertex to meet C_D(W) in exactly O₂(D). The common
Sylow intersection and the odd-order theorem make C_D(W) solvable.

The two vertex images have common Sylow subgroups of index three.
They cannot coincide, since their residual images do not normalize one
another. Thus D/C_D(W) is a Goldschmidt triple with the full original
overlap and trivial two-core. The first isomorphism theorem identifies
its amalgam with the original three quotients by O₂(D), compatibly with
both inclusions. The order-four chief interval supplies every premise.

This establishes the kernel reduction used at the beginning of 14.5.8;
solvability of the entire D and the later containment argument remain.
Source: Aschbacher–Smith, F.6.7–8, printed p.305; 14.5.6–8,
printed pp.1014–1015; 14.7.20, printed p.1049, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u

private theorem CubicActionQuotient_action_kernel_intersections
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B)
    (C : Subgroup D) [C.Normal] (hQC : pCore 2 D ≤ C)
    (hout : ¬ ((pResidual 2 B).map B.subtype).map (QuotientGroup.mk' C) ≤
      normalizer (((pResidual 2 A).map A.subtype).map (QuotientGroup.mk' C) : Set _)) :
    A ⊓ C = pCore 2 D ∧ B ⊓ C = pCore 2 D ∧ Group.IsSolvable C := by
  let q := QuotientGroup.mk' C
  have hAC : A ⊓ C ≤ (pCore 2 A).map A.subtype := by
    apply (ht.left_subnormal_core_iff_not_residual_le C (Normal.isSubnormal inferInstance)).mpr
    intro hle
    have hz : ((pResidual 2 A).map A.subtype).map q = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (by simpa only [q,QuotientGroup.ker_mk'] using hle)
    apply hout
    rw [hz,normalizer_eq_top]
    exact le_top
  have hBC : B ⊓ C ≤ (pCore 2 B).map B.subtype := by
    apply (ht.right_subnormal_core_iff_not_residual_le C (Normal.isSubnormal inferInstance)).mpr
    intro hle
    have hz : ((pResidual 2 B).map B.subtype).map q = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (by simpa only [q,QuotientGroup.ker_mk'] using hle)
    apply hout
    rw [hz]
    exact bot_le
  have hTC : (A ⊓ B) ⊓ C = pCore 2 D := le_antisymm
    (ht.normal_intersection_le_twoCore C hAC hBC)
    (le_inf ht.twoCore_isGreatest.1.1 hQC)
  have hA := ht.left_intersection_eq_core_intersection C hAC
  have hB := ht.symm.left_intersection_eq_core_intersection C hBC
  have hsol : Group.IsSolvable (C ⧸ (pCore 2 D).subgroupOf C) := by
    have hh := ht.normal_quotient_solvable C hAC hBC
    rwa [sup_eq_left.mpr hQC] at hh
  let : Group.IsNilpotent ((pCore 2 D).subgroupOf C) :=
    (pCore_isPGroup (p := 2) (G := D)).comap_subtype.isNilpotent
  exact ⟨hA.1.trans (hA.2.trans hTC),
    hB.1.trans (hB.2.trans (by simpa only [inf_comm B A] using hTC)),
    (Group.isSolvable_iff_subgroup_quotient ((pCore 2 D).subgroupOf C)).mpr
      ⟨inferInstance,hsol⟩⟩

private def CubicActionQuotient_action_local_quotient_equiv
    {D E : Type*} [Group D] [Finite D] [Group E] [Finite E]
    (f : D →* E) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    (D ⧸ pCore 2 D) ≃* (E ⧸ pCore 2 E) := by
  let q := (QuotientGroup.mk' (pCore 2 E)).comp f
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hf
  have he : q.ker = pCore 2 D := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact f.comap_pCore_of_ker_isPGroup hf hk
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)

private theorem CubicActionQuotient_action_intermediate {D : Type*} [Group D] {A B C : Subgroup D}
    (hAB : A ≤ B) (hBC : B ≤ C) (hi : A.relIndex C = 3) : B = A ∨ B = C := by
  have hm := relIndex_mul_relIndex A B C hAB hBC
  rw [hi] at hm
  have hp : (A.relIndex B * B.relIndex C).Prime := hm ▸ Nat.prime_three
  rcases Nat.prime_mul_iff.mp hp with ⟨_,hB⟩ | ⟨_,hA⟩
  · exact Or.inr (le_antisymm hBC (relIndex_eq_one.mp hB))
  · exact Or.inl (le_antisymm (relIndex_eq_one.mp hA) hAB)

private theorem CubicActionQuotient_action_quotient_triple
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B)
    (C : Subgroup D) [C.Normal] (hQC : pCore 2 D ≤ C)
    (hout : ¬ ((pResidual 2 B).map B.subtype).map (QuotientGroup.mk' C) ≤
      normalizer (((pResidual 2 A).map A.subtype).map (QuotientGroup.mk' C) : Set _)) :
    let q := QuotientGroup.mk' C
    A.map q ⊓ B.map q = (A ⊓ B).map q ∧
      ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) := by
  let q := QuotientGroup.mk' C
  obtain ⟨hAC,hBC,_⟩ := CubicActionQuotient_action_kernel_intersections ht C hQC hout
  have hlocal (J : Subgroup D) (hj : J ⊓ C = pCore 2 D)
      (e : Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3))) :
      Nonempty (((J.map q) ⧸ pCore 2 (J.map q)) ≃* Equiv.Perm (Fin 3)) := by
    have hk : IsPGroup 2 (q.subgroupMap J).ker := by
      rw [ker_subgroupMap,QuotientGroup.ker_mk']
      have he : C.subgroupOf J = (pCore 2 D).subgroupOf J := by
        ext x
        change (x : D) ∈ C ↔ (x : D) ∈ pCore 2 D
        rw [←hj]
        exact (and_iff_right x.property).symm
      rw [he]
      exact pCore_isPGroup.comap_subtype
    exact ⟨(CubicActionQuotient_action_local_quotient_equiv _ (q.subgroupMap_surjective J) hk).symm.trans e.some⟩
  have hA := hlocal A hAC ht.quotient_left
  have hB := hlocal B hBC ht.quotient_right
  obtain ⟨T,hT⟩ := ht.intersection_sylow
  let S := T.mapSurjective (QuotientGroup.mk'_surjective C)
  have hS : (S : Subgroup _) = (A ⊓ B).map q := by
    change (T : Subgroup D).map q = _
    rw [hT]
  have hSA : (S : Subgroup _) ≤ A.map q := hS ▸ map_mono inf_le_left
  have hSB : (S : Subgroup _) ≤ B.map q := hS ▸ map_mono inf_le_right
  have hAi : (S : Subgroup _).relIndex (A.map q) = 3 :=
    SymmetricThreeTwoCore.sylow_index_three hA.some (S.subtype hSA)
  have hBi : (S : Subgroup _).relIndex (B.map q) = 3 :=
    SymmetricThreeTwoCore.sylow_index_three hB.some (S.subtype hSB)
  have hi : A.map q ⊓ B.map q = (A ⊓ B).map q := by
    rcases CubicActionQuotient_action_intermediate (le_inf hSA hSB) inf_le_left hAi with hI | heA
    · exact hI.trans hS
    rcases CubicActionQuotient_action_intermediate (le_inf hSA hSB) inf_le_right hBi with hI | heB
    · exact hI.trans hS
    have he : A.map q = B.map q := heA.symm.trans heB
    apply False.elim
    apply hout
    rw [map_embedded_pResidual,map_embedded_pResidual,he]
    exact ((pResidual 2 (B.map q)).map (B.map q).subtype).le_normalizer
  refine ⟨hi,?_,hA,hB,S,?_⟩
  · rw [←Subgroup.map_sup,ht.generated,map_top_of_surjective q (QuotientGroup.mk'_surjective C)]
  · exact hi.trans hS.symm

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The intrinsic residuals of the two original vertices, in the generated
group, are exactly the restrictions of L₂ and Y. -/
theorem cubic_action_residuals
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let A := (F.P L).subgroupOf D
    let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
    (pResidual 2 A).map A.subtype = (F.Li L 2).subgroupOf D ∧
      (pResidual 2 B).map B.subtype = Y.subgroupOf D := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  have hPD : F.P L ≤ D := le_sup_left
  have hBD : Y ⊔ (T : Subgroup G) ≤ D := le_sup_right
  have hYD : Y ≤ D := le_sup_left.trans hBD
  have hXD : F.Li L 2 ≤ D := by
    apply le_trans _ hPD
    rw [plane_parabolic_eq_join h structural]
    exact le_sup_left
  constructor
  · apply (map_injective D.subtype_injective)
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hPD,
      plane_parabolic_residual h structural,map_subgroupOf_eq_of_le hXD]
  · apply (map_injective D.subtype_injective)
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hBD,
      embedded_pResidual_join_pGroup Y _ hYp T.isPGroup' hYT,
      map_subgroupOf_eq_of_le hYD]

/-- Both original vertices meet the point-span centralizer in exactly O₂(D).
The centralizer is solvable, as required in the first step of 14.5.8. -/
theorem cubic_generated_action_kernel_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    let C := centralizer (W.subgroupOf D : Set D)
    (F.P L).subgroupOf D ⊓ C = pCore 2 D ∧
      (Y ⊔ (T : Subgroup G)).subgroupOf D ⊓ C = pCore 2 D ∧
      Group.IsSolvable C := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  have hWC := (cubic_generated_local_structure h hab structural previous Y hYH he).2.2.2.2
  have hQC : pCore 2 D ≤ centralizer (W.subgroupOf D : Set D) := by
    intro x hx w hw
    apply Subtype.ext
    exact (le_centralizer_iff.mp hWC) (mem_map_of_mem D.subtype hx) w hw
  apply CubicActionQuotient_action_kernel_intersections (cubic_goldschmidt_triple h structural Y hYH he)
    _ hQC
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  rw [hr.1,hr.2]
  exact cubic_generated_action_normalizer_obstruction_of_normalizes_point h structural Y hYH hYL hout

/-- The original full point-normality interface. -/
theorem cubic_generated_action_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    let C := centralizer (W.subgroupOf D : Set D)
    (F.P L).subgroupOf D ⊓ C = pCore 2 D ∧
      (Y ⊔ (T : Subgroup G)).subgroupOf D ⊓ C = pCore 2 D ∧
      Group.IsSolvable C := by
  apply cubic_generated_action_kernel_of_normalizes_point h hab structural previous Y hYH _ hYp hYT hout he
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The literal conjugation quotient retains the full original overlap and
is a Goldschmidt triple with trivial two-core. The nonnormalizing residual
images rule out collapse of its two vertices. -/
theorem cubic_generated_action_triple_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    ((F.P L).subgroupOf D).map q ⊓ ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q =
        ((T : Subgroup G).subgroupOf D).map q ∧
      ChapterF.IsGoldschmidtTriple ((F.P L).subgroupOf D |>.map q)
        ((Y ⊔ (T : Subgroup G)).subgroupOf D |>.map q) ∧
      pCore 2 (D ⧸ C) = ⊥ := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  have hQC : pCore 2 D ≤ C := by
    intro x hx
    have hh := (cubic_generated_action_kernel_of_normalizes_point h hab structural previous
      Y hYH hYL hYp hYT hout he).1
    rw [←hh] at hx
    exact hx.2
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  have ho : ¬ ((pResidual 2 ((Y ⊔ (T : Subgroup G)).subgroupOf D)).map
      ((Y ⊔ (T : Subgroup G)).subgroupOf D).subtype).map (QuotientGroup.mk' C) ≤
      normalizer (((pResidual 2 ((F.P L).subgroupOf D)).map
        ((F.P L).subgroupOf D).subtype).map (QuotientGroup.mk' C) : Set _) := by
    rw [hr.1,hr.2]
    exact cubic_generated_action_normalizer_obstruction_of_normalizes_point h structural Y hYH hYL hout
  obtain ⟨hi,ht⟩ := CubicActionQuotient_action_quotient_triple
    (cubic_goldschmidt_triple h structural Y hYH he) C hQC ho
  have hinter : (F.P L).subgroupOf D ⊓ (Y ⊔ (T : Subgroup G)).subgroupOf D =
      (T : Subgroup G).subgroupOf D := by
    apply le_antisymm
    · intro x hx
      have hh : (x : G) ∈ F.P L ⊓ F.H :=
        ⟨hx.1,(sup_le hYH (F.invariant 1)) hx.2⟩
      rwa [plane_parabolic_inf_point h structural] at hh
    · intro x hx
      exact ⟨F.binary_sylow_le_P L hx,
        (le_sup_right : (T : Subgroup G) ≤ Y ⊔ (T : Subgroup G)) hx⟩
  rw [hinter] at hi
  exact ⟨hi,ht,(cubic_generated_span_reduced h hab structural previous Y hYH he).quotient_pCore_eq_bot⟩

private def CubicActionQuotient_action_kernel_equiv
    {D : Type*} [Group D] [Finite D] (C : Subgroup D) [C.Normal]
    (J : Subgroup D) (hj : J ⊓ C = pCore 2 D) :
    (J ⧸ (QuotientGroup.mk' (pCore 2 D)).ker.subgroupOf J) ≃*
      J.map (QuotientGroup.mk' C) :=
  (QuotientGroup.quotientMulEquivOfEq (by
    rw [ker_subgroupMap,QuotientGroup.ker_mk',QuotientGroup.ker_mk']
    ext x
    change (x : D) ∈ pCore 2 D ↔ (x : D) ∈ C
    rw [←hj]
    exact and_iff_right x.property)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk' C).subgroupMap_surjective J))

/-- The original full point-normality interface. -/
theorem cubic_generated_action_triple
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    ((F.P L).subgroupOf D).map q ⊓ ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q =
        ((T : Subgroup G).subgroupOf D).map q ∧
      ChapterF.IsGoldschmidtTriple ((F.P L).subgroupOf D |>.map q)
        ((Y ⊔ (T : Subgroup G)).subgroupOf D |>.map q) ∧
      pCore 2 (D ⧸ C) = ⊥ := by
  apply cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH _ hYp hYT hout he
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The action amalgam is compatibly isomorphic to the original three
quotients by O₂(D). Both inclusion squares use the actual quotient maps. -/
def cubicActionAmalgamIsoOfNormalizesPoint
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let A := (F.P L).subgroupOf D
    let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
    Theory.GroupTheory.RankTwoAmalgam.Iso
      (Theory.GroupTheory.RankTwoAmalgam.ofSubgroupQuotients
        (QuotientGroup.mk' (pCore 2 D)) A (A ⊓ B) B inf_le_left inf_le_right)
      (Theory.GroupTheory.RankTwoAmalgam.ofSubgroups
        (A.map q) ((A ⊓ B).map q) (B.map q)
        (map_mono inf_le_left) (map_mono inf_le_right)) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let A := (F.P L).subgroupOf D
  let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  obtain ⟨hAC,hBC,_⟩ := cubic_generated_action_kernel_of_normalizes_point h hab structural previous
    Y hYH hYL hYp hYT hout he
  have hTC : (A ⊓ B) ⊓ C = pCore 2 D := by
    apply le_antisymm ((inf_le_inf inf_le_left le_rfl).trans_eq hAC)
    exact le_inf (cubic_goldschmidt_triple h structural Y hYH he).twoCore_isGreatest.1.1
      (hAC ▸ (inf_le_right : A ⊓ C ≤ C))
  exact {
    left := CubicActionQuotient_action_kernel_equiv C A hAC
    middle := CubicActionQuotient_action_kernel_equiv C (A ⊓ B) hTC
    right := CubicActionQuotient_action_kernel_equiv C B hBC
    left_commutes := fun b => by
      obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective _ b
      rfl
    right_commutes := fun b => by
      obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective _ b
      rfl }

/-- The original full point-normality interface. -/
def cubicActionAmalgamIso
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let A := (F.P L).subgroupOf D
    let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
    Theory.GroupTheory.RankTwoAmalgam.Iso
      (Theory.GroupTheory.RankTwoAmalgam.ofSubgroupQuotients
        (QuotientGroup.mk' (pCore 2 D)) A (A ⊓ B) B inf_le_left inf_le_right)
      (Theory.GroupTheory.RankTwoAmalgam.ofSubgroups
        (A.map q) ((A ⊓ B).map q) (B.map q)
        (map_mono inf_le_left) (map_mono inf_le_right)) := by
  apply cubicActionAmalgamIsoOfNormalizesPoint h hab structural previous Y hYH _ hYp hYT hout he
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement in
/-- The actual order-four chief interval supplies a faithful Goldschmidt
action quotient and its solvable kernel. All earlier point-normality and
cubic-quotient premises are discharged from the original extraspecial branch. -/
theorem extraspecial_four_interval_cubic_action
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 ∧
      Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      let A := (F.P L).subgroupOf D
      let B := (Y ⊔ (T : Subgroup G)).subgroupOf D
      let W := conjugateSpanBy (F.Vi 1) D
      letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy _ _)
      let C := centralizer (W.subgroupOf D : Set D)
      let q := QuotientGroup.mk' C
      A ⊓ C = pCore 2 D ∧ B ⊓ C = pCore 2 D ∧ Group.IsSolvable C ∧
      A.map q ⊓ B.map q = ((T : Subgroup G).subgroupOf D).map q ∧
      ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) ∧ pCore 2 (D ⧸ C) = ⊥ ∧
      Nonempty (Theory.GroupTheory.RankTwoAmalgam.Iso
        (Theory.GroupTheory.RankTwoAmalgam.ofSubgroupQuotients
          (QuotientGroup.mk' (pCore 2 D)) A (A ⊓ B) B inf_le_left inf_le_right)
        (Theory.GroupTheory.RankTwoAmalgam.ofSubgroups
          (A.map q) ((A ⊓ B).map q) (B.map q)
          (map_mono inf_le_left) (map_mono inf_le_right))) := by
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he⟩ :=
    extraspecial_four_interval_escaping_symmetricThree h hab structural previous hex hcard hexp
      N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨hAC,hBC,hsol⟩ := cubic_generated_action_kernel h hab structural previous hn
    Y hYH hYp hYT hout he
  obtain ⟨hi,ht,hcore⟩ := cubic_generated_action_triple h hab structural previous hn
    Y hYH hYp hYT hout he
  exact ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,hAC,hBC,hsol,hi,ht,hcore,
    ⟨cubicActionAmalgamIso h hab structural previous hn Y hYH hYp hYT hout he⟩⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Faithful components in the original cubic completion

The solvable centralizer C_D(W) cannot contain a C-component. The actual
reduced point span W therefore proves faithfulness in the original local
family. Earlier 14.3.4 supplies the genuine A₅ or PSL₃(2) quotient,
maximality, and relative normality in the Sylow join.

The component's radical is precisely its two-core. Hence its kernel on
W is exactly that two-core, so the model quotient is its literal image
in D/C_D(W). Applying the proved F.6.10 to this action quotient gives
normality in D and the two source orientations for residual containment
and generation. The final application supplies these facts for the
escaping cubic from the actual order-four chief interval.

EarlierFaithfulClassification is the named earlier 14.3.4 input; its
producer and final discharge remain qt-d-1434-source and qt-d-14775-source.
The nonsolvable alternatives still need exclusion to prove 14.5.8 and
complete the containment argument; this module does not assert solvability.
Source: Aschbacher–Smith, 14.5.8, printed pp.1014–1015, using
1.2.6/10, 14.3.4 and F.6.10; 14.7.20, p.1049, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

open ChapterA.Section04 Theory.GroupTheory in
/-- Every C-component of the original cubic completion belongs to the
faithful local family: its action on the actual reduced point span is
nontrivial because the centralizer is solvable. -/
theorem cubic_generated_component_faithful_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    J.map D.subtype ∈ Chapter1.L G (T : Subgroup G) ∧
      IsFaithfulSignalizerType (J.map D.subtype) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let C := centralizer (W.subgroupOf D : Set D)
  let JG := J.map D.subtype
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hJD : JG ≤ D := map_subtype_le J
  have hJDG : JG.subgroupOf D = J := comap_map_eq_self_of_injective D.subtype_injective J
  have hDH : D ∈ Chapter1.H G := by
    intro hz
    apply cubic_generated_core_ne_bot h hab structural previous Y hYH he
    exact ((pCore 2 D).map_eq_bot_iff_of_injective D.subtype_injective).mp hz
  have hJL : JG ∈ Chapter1.L G (T : Subgroup G) := Chapter1.mem_L_of_cComponent hDH
    ⟨T.subtype hTD,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTD]⟩
    hJD (hJDG ▸ hJ)
  have hp : IsPPerfect 2 J :=
    (Chapter1.Section02.Adequate.mem_L_isPPerfect hJL).of_surjective
      (J.equivMapOfInjective D.subtype D.subtype_injective).symm.toMonoidHom
      (J.equivMapOfInjective D.subtype D.subtype_injective).symm.surjective
  let : Group.IsSolvable C := (cubic_generated_action_kernel_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he).2.2
  have hnot : ¬ J ≤ C := by
    intro hj
    exact hJ.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := inclusion hj) (inclusion_injective hj))
  have hmod : intrinsicSignalizerModule J ≠ ⊥ := by
    intro hz
    apply hnot
    have hmove : ⁅W.subgroupOf D,J⁆ = ⊥ := by
      apply bot_unique
      exact (commutator_mono
        (cubic_generated_span_reduced h hab structural previous Y hYH he).le_reducedPSubgroup
        le_rfl).trans ((reduced_commutator_le_intrinsicModule J hJ.subnormal hp).trans hz.le)
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hmove)
  refine ⟨hJL,Chapter1.Section02.Adequate.mem_L_isSignalizerType T
    (h.source.simpleQTKE.evenCharacteristic T) hJL,?_⟩
  rw [intrinsicSignalizerModule_map_of_injective D.subtype D.subtype_injective J]
  exact fun hz => hmod (((intrinsicSignalizerModule J).map_eq_bot_iff_of_injective
    D.subtype_injective).mp hz)

open ChapterA.Section04 Theory.GroupTheory in
/-- The original full point-normality interface. -/
theorem cubic_generated_component_faithful
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    J.map D.subtype ∈ Chapter1.L G (T : Subgroup G) ∧
      IsFaithfulSignalizerType (J.map D.subtype) := by
  apply cubic_generated_component_faithful_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (Y := Y)
    (hYH := hYH) (hYp := hYp) (hYT := hYT) (hout := hout)
    (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open ChapterA.Section04 Chapter14.Section04.LargerDimension.LocalAction.Components in
/-- In the nonsolvable branch of 14.5.8, the original completion has an
actual faithful C-component with quotient A₅ or PSL₃(2). Only the named
earlier 14.3.4 classification remains explicit. -/
theorem cubic_generated_nonsolvable_component_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (hns : ¬ Group.IsSolvable (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    ∃ J : Subgroup G, J ≤ D ∧ (J.subgroupOf D).IsCComponent ∧
      J ∈ Chapter1.LStar G (T : Subgroup G) ∧ IsFaithfulSignalizerType J ∧
      (J.subgroupOf (J ⊔ (T : Subgroup G))).Normal ∧
      (Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∨
        Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL)) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  obtain ⟨J,hJ⟩ := exists_isCComponent_of_not_isSolvable hns
  obtain ⟨hJL,hJf⟩ := cubic_generated_component_faithful_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨hmodel,hnJ,hmax⟩ := faithful (J.map D.subtype) hJL hJf
  refine ⟨J.map D.subtype,map_subtype_le J,?_,hmax,hJf,hnJ,hmodel⟩
  change ((J.map D.subtype).subgroupOf D).IsCComponent
  simpa only [subgroupOf,comap_map_eq_self_of_injective D.subtype_injective] using hJ

open ChapterA.Section04 Chapter14.Section04.LargerDimension.LocalAction.Components in
/-- The original full point-normality interface. -/
theorem cubic_generated_nonsolvable_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (hns : ¬ Group.IsSolvable (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G)) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    ∃ J : Subgroup G, J ≤ D ∧ (J.subgroupOf D).IsCComponent ∧
      J ∈ Chapter1.LStar G (T : Subgroup G) ∧ IsFaithfulSignalizerType J ∧
      (J.subgroupOf (J ⊔ (T : Subgroup G))).Normal ∧
      (Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∨
        Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL)) := by
  apply cubic_generated_nonsolvable_component_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (hns := hns)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open Chapter14.Section04.LargerDimension.LocalAction.Components Theory.GroupTheory in
/-- The selected component has its exact two-core as kernel on W. Thus its
source A₅ or PSL₃(2) quotient is the actual image in D/C_D(W). -/
theorem cubic_generated_component_action_kernel_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
    (q.subgroupMap J).ker = pCore 2 J ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* J.map q) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  let JG := J.map D.subtype
  obtain ⟨hJL,hJf⟩ := cubic_generated_component_faithful_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he J hJ
  have hm := (faithful JG hJL hJf).1
  let : IsSimpleGroup (JG ⧸ pCore 2 JG) := by
    rcases hm with he | he
    · let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact he.some.isSimpleGroup
    · let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
      exact he.some.isSimpleGroup
  let eJ := J.equivMapOfInjective D.subtype D.subtype_injective
  let eQ := QuotientGroup.congr (pCore 2 J) (pCore 2 JG) eJ (pCore_map_iso 2 eJ)
  let : IsSimpleGroup (J ⧸ pCore 2 J) := eQ.isSimpleGroup
  let := hJ.perfect
  have hrad : solvableRadical J = pCore 2 J :=
    PerfectCoreTwoExtension.radical_eq_core
  have htop : (⊤ : Subgroup J).IsCComponent := by
    simpa only [subgroupOf_self] using hJ.subgroupOf le_rfl
  let : Group.IsSolvable C := (cubic_generated_action_kernel_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he).2.2
  have hnot : ¬ J ≤ C := by
    intro hj
    exact hJ.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := inclusion hj) (inclusion_injective hj))
  have hkne : (q.subgroupMap J).ker ≠ ⊤ := by
    intro hz
    apply hnot
    intro x hx
    have hh : (⟨x,hx⟩ : J) ∈ (q.subgroupMap J).ker := hz.symm ▸ mem_top _
    exact (QuotientGroup.eq_one_iff x).mp (congrArg Subtype.val hh)
  have hQC : pCore 2 D ≤ C :=
    ((cubic_generated_action_kernel_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he).1.symm.le).trans inf_le_right
  have hk : (q.subgroupMap J).ker = pCore 2 J := by
    apply le_antisymm
    · exact (kernel_le_solvableRadical_of_top_isCComponent htop _ hkne).trans hrad.le
    · rw [ker_subgroupMap,QuotientGroup.ker_mk']
      exact (pCore_subnormal_eq_comap 2 hJ.subnormal).le.trans (comap_mono hQC)
  exact ⟨hk,⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (q.subgroupMap_surjective J))⟩⟩

open Chapter14.Section04.LargerDimension.LocalAction.Components Theory.GroupTheory in
/-- The original full point-normality interface. -/
theorem cubic_generated_component_action_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
    (q.subgroupMap J).ker = pCore 2 J ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* J.map q) := by
  apply cubic_generated_component_action_kernel_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open Chapter14.Section04.LargerDimension.LocalAction.Components Theory.GroupTheory in
/-- The source F.6.10 reduction applies to the actual action image of each
component. It proves normality back in D, and retains the two possible
orientations of residual containment and generation in D/C_D(W). -/
theorem cubic_generated_component_action_reduction_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    J.Normal ∧ IsComponent (D ⧸ C) (J.map q) ∧ (J.map q).Normal ∧
      ((((F.Li L 2).subgroupOf D).map q ≤ J.map q ∧
        J.map q ⊔ ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q = ⊤) ∨
       ((Y.subgroupOf D).map q ≤ J.map q ∧
        J.map q ⊔ ((F.P L).subgroupOf D).map q = ⊤)) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  let JG := J.map D.subtype
  obtain ⟨hJL,hJf⟩ := cubic_generated_component_faithful_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he J hJ
  have hm := (faithful JG hJL hJf).1
  let : IsSimpleGroup (JG ⧸ pCore 2 JG) := by
    rcases hm with he | he
    · let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact he.some.isSimpleGroup
    · let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
      exact he.some.isSimpleGroup
  let eJ := J.equivMapOfInjective D.subtype D.subtype_injective
  let eQ := QuotientGroup.congr (pCore 2 J) (pCore 2 JG) eJ (pCore_map_iso 2 eJ)
  let : IsSimpleGroup (J ⧸ pCore 2 J) := eQ.isSimpleGroup
  obtain ⟨_,⟨e⟩⟩ := cubic_generated_component_action_kernel_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  let : IsSimpleGroup (J.map q) := e.symm.isSimpleGroup
  let := hJ.perfect
  let : Group.IsPerfect (J.map q) := Group.IsPerfect.map q
  have hcenter : center (J.map q) = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (J.map q)) inferInstance).resolve_right
      (fun hz => Group.IsPerfect.not_isMulCommutative (J.map q) (center_eq_top_iff.mp hz))
  let : IsQuasisimple (J.map q) := ⟨((QuotientGroup.quotientMulEquivOfEq hcenter).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hj : IsComponent (D ⧸ C) (J.map q) :=
    ⟨hJ.subnormal.map (QuotientGroup.mk'_surjective C),inferInstance⟩
  obtain ⟨_,ht,hcore⟩ := cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he
  have hSQ := (cubic_generated_local_structure h hab structural previous Y hYH he).2.1
  obtain ⟨hnq,hcases⟩ := ChapterF.SourceAssembly.source_component_reduction
    (ChapterA.Section02.theoremA_knownSimple (G := D)) hSQ q (QuotientGroup.mk'_surjective C)
    ht hcore hj
  let : Group.IsSolvable C := (cubic_generated_action_kernel_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he).2.2
  have hnJ := cComponent_normal_of_quotient_normal hJ C hnq
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  rw [←map_embedded_pResidual,←map_embedded_pResidual,hr.1,hr.2] at hcases
  exact ⟨hnJ,hj,hnq,hcases⟩

open Chapter14.Section04.LargerDimension.LocalAction.Components Theory.GroupTheory in
/-- The original full point-normality interface. -/
theorem cubic_generated_component_action_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    J.Normal ∧ IsComponent (D ⧸ C) (J.map q) ∧ (J.map q).Normal ∧
      ((((F.Li L 2).subgroupOf D).map q ≤ J.map q ∧
        J.map q ⊔ ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q = ⊤) ∨
       ((Y.subgroupOf D).map q ≤ J.map q ∧
        J.map q ⊔ ((F.P L).subgroupOf D).map q = ⊤)) := by
  apply cubic_generated_component_action_reduction_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04
  Chapter14.Section04.LargerDimension.LocalAction.Components in
/-- The original order-four interval reduces solvability of its cubic
completion to the two actual faithful component models of 14.3.4. -/
theorem extraspecial_four_interval_cubic_component_alternative
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 ∧
      Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      let W := conjugateSpanBy (F.Vi 1) D
      letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy _ _)
      let q := QuotientGroup.mk' (centralizer (W.subgroupOf D : Set D))
      Group.IsSolvable D ∨ ∃ J : Subgroup G, ∃ _hJD : J ≤ D,
        (J.subgroupOf D).IsCComponent ∧ (J.subgroupOf D).Normal ∧
        J ∈ Chapter1.LStar G (T : Subgroup G) ∧ IsFaithfulSignalizerType J ∧
        (J.subgroupOf (J ⊔ (T : Subgroup G))).Normal ∧
        (Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∨
          Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL)) ∧
        (q.subgroupMap (J.subgroupOf D)).ker = pCore 2 (J.subgroupOf D) ∧
        Nonempty ((J ⧸ pCore 2 J) ≃* (J.subgroupOf D).map q) ∧
        Theory.GroupTheory.IsComponent (D ⧸ centralizer (W.subgroupOf D : Set D)) ((J.subgroupOf D).map q) ∧
        ((J.subgroupOf D).map q).Normal ∧
        ((((F.Li L 2).subgroupOf D).map q ≤ (J.subgroupOf D).map q ∧
          (J.subgroupOf D).map q ⊔ ((Y ⊔ (T : Subgroup G)).subgroupOf D).map q = ⊤) ∨
         ((Y.subgroupOf D).map q ≤ (J.subgroupOf D).map q ∧
          (J.subgroupOf D).map q ⊔ ((F.P L).subgroupOf D).map q = ⊤)) := by
  classical
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he⟩ :=
    extraspecial_four_interval_escaping_symmetricThree h hab structural previous hex hcard hexp
      N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  refine ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,?_⟩
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  by_cases hs : Group.IsSolvable D
  · exact Or.inl hs
  right
  obtain ⟨J,hJD,hJ,hmax,hf,hnJ,hmodel⟩ := cubic_generated_nonsolvable_component
    h hab structural previous faithful hn Y hYH hYp hYT hout he hs
  obtain ⟨hk,⟨e⟩⟩ := cubic_generated_component_action_kernel h hab structural previous faithful hn
    Y hYH hYp hYT hout he (J.subgroupOf D) hJ
  let eJ := subgroupOfEquivOfLe hJD
  let eQ := QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)
  obtain ⟨hnD,himage,hnimage,hcases⟩ := cubic_generated_component_action_reduction
    h hab structural previous faithful hn Y hYH hYp hYT hout he (J.subgroupOf D) hJ
  exact ⟨J,hJD,hJ,hnD,hmax,hf,hnJ,hmodel,hk,⟨eQ.symm.trans e⟩,himage,hnimage,hcases⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The surviving linear action of the original cubic completion

A normal A₅ component in the faithful action quotient is impossible.
Each solvable vertex normalizes its intersection with a Sylow four-group:
that intersection is the two-core of the corresponding proper subgroup
of A₅. The common-normal-subgroup property of the Goldschmidt triple
would then put this four-group in the trivial ambient two-core.

For a PSL₃(2) component, a cubic residual outside the component preserves
its Sylow subgroup and hence acts trivially, by the two-group automorphism
stabilizer. This contradicts the original nonnormalization obstruction.
Thus both cubic residuals lie in the component and generate the whole
action residual. The original Sylow preserves a parabolic of PSL₃(2),
so its action is inner. Triviality of the component centralizer then
identifies the entire action quotient D/C_D(W) with PSL₃(2).

The final application retains the escaping cubic from the actual
order-four chief interval, both original generators and all exact kernels.
The natural-module and ambient geometric exclusion of the remaining
PSL₃(2) case is still needed for solvability of D. Earlier 14.3.4 remains
the named independent faithful-classification input.

Source: Aschbacher–Smith, proof of 14.5.8, printed pp.1014–1015,
and its use in 14.7.20(2), printed p.1049, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
universe u

private theorem CubicLinearAction_alternating_normal_sylow_intersection
    {D : Type*} [Group D] [Finite D]
    (S : Sylow 2 D) (J A : Subgroup D) [J.Normal] [Group.IsSolvable A]
    (e : J ≃* alternatingGroup (Fin 5)) (hSA : (S : Subgroup D) ≤ A) :
    A ≤ normalizer (((S : Subgroup D) ⊓ J : Subgroup D) : Set D) := by
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal J
  let B := A.subgroupOf J
  have hRB : (R : Subgroup J) ≤ B := by rw [hR]; exact comap_mono hSA
  have hBA : B.map J.subtype ≤ A := (subgroupOf_map_subtype A J).le.trans inf_le_left
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := (inclusion hBA).comp
      (B.equivMapOfInjective J.subtype J.subtype_injective).toMonoidHom)
    ((inclusion_injective hBA).comp (B.equivMapOfInjective J.subtype J.subtype_injective).injective)
  have hBN := alternatingGroup.solvable_sylow_overgroup_le_normalizer_of_equiv e R B hRB
  have hcore : B.pCoreIn 2 = (R : Subgroup J) := by
    apply le_antisymm
    · have hh := pCoreIn_le_sylow B (R.subtype hRB)
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hRB] using hh
    · exact le_pCoreIn_of_normalizes R.isPGroup' hRB hBN
  have he : (A ⊓ J).pCoreIn 2 = (S : Subgroup D) ⊓ J := by
    have hh := congrArg (map J.subtype) hcore
    rw [map_pCoreIn_of_injective 2 _ _ J.subtype_injective,
      subgroupOf_map_subtype,hR,subgroupOf_map_subtype] at hh
    exact hh
  rw [←he]
  exact ((le_inf A.le_normalizer le_normalizer_of_normal).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (A ⊓ J) (pCore 2 (A ⊓ J : Subgroup D)))

private theorem CubicLinearAction_goldschmidt_no_alternating_normal
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : CFSG.Quasithin.ChapterF.IsGoldschmidtTriple A B)
    (hcore : pCore 2 D = ⊥) (J : Subgroup D) [J.Normal]
    (e : J ≃* alternatingGroup (Fin 5)) : False := by
  let : Group.IsSolvable A := SymmetricThreeTwoCore.solvable ht.quotient_left.some
  let : Group.IsSolvable B := SymmetricThreeTwoCore.solvable ht.quotient_right.some
  obtain ⟨S,hS⟩ := ht.intersection_sylow
  have hSA : (S : Subgroup D) ≤ A := hS.symm.le.trans inf_le_left
  have hSB : (S : Subgroup D) ≤ B := hS.symm.le.trans inf_le_right
  have hA := CubicLinearAction_alternating_normal_sylow_intersection S J A e hSA
  have hB := CubicLinearAction_alternating_normal_sylow_intersection S J B e hSB
  have hbot : (S : Subgroup D) ⊓ J = ⊥ :=
    ht.common_normal_eq_bot hcore _ (inf_le_left.trans hS.ge)
      (normal_subgroupOf_of_le_normalizer hA) (normal_subgroupOf_of_le_normalizer hB)
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal J
  have hRbot : (R : Subgroup J) = ⊥ := by
    apply map_injective J.subtype_injective
    rw [hR,subgroupOf_map_subtype,hbot,Subgroup.map_bot]
  have hc := Theory.PSL2.SylowFixedQuotients.alternating_sylow_card
    (R.mapSurjective (f := e.toMonoidHom) e.surjective)
  change Nat.card ((R : Subgroup J).map e.toMonoidHom) = 4 at hc
  simp [hRbot] at hc

private theorem CubicLinearAction_goldschmidt_escaping_residual_centralizes_linear
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B) (J : Subgroup D) [J.Normal]
    (e : J ≃* Matrix.PSL3Two.PSL)
    (hout : ¬ (pResidual 2 B).map B.subtype ≤ J) :
    (pResidual 2 B).map B.subtype ≤ centralizer (J : Set D) := by
  let R := (pResidual 2 B).map B.subtype
  obtain ⟨S,hS⟩ := ht.intersection_sylow
  have hSB : (S : Subgroup D) ≤ B := hS.symm.le.trans inf_le_right
  have hBJ : B ≤ normalizer (J : Set D) := le_normalizer_of_normal
  have hJB : IsPGroup 2 (J ⊓ B : Subgroup D) := by
    have hh := (ht.right_subnormal_core_iff_not_residual_le J
      (Normal.isSubnormal inferInstance)).mpr hout
    exact (pCore_isPGroup.map B.subtype).to_le ((inf_comm J B).le.trans hh)
  let f : J ≃* Matrix.PSL3Two.SL := e.trans Matrix.PSL3Two.equiv.symm
  let a : B →* MulAut Matrix.PSL3Two.SL := (MulAut.congr f).toMonoidHom.comp
    (J.normalizerMonoidHom.comp (inclusion hBJ))
  have ha (x : B) (k : J) : a x (f k) =
      f (J.normalizerMonoidHom ⟨x,hBJ x.property⟩ k) := by
    change f (J.normalizerMonoidHom ⟨x,hBJ x.property⟩ (f.symm (f k))) = _
    rw [f.symm_apply_apply]
  have htriv := NormalSylowQuotientAction.pPerfect_action_eq_one S J B R
    hBJ hSB hJB (map_subtype_le _) (isPPerfect_embedded_pResidual 2 B)
    f.toMonoidHom f.surjective a ha Matrix.PSL3Two.automorphism_sylow_stabilizer_two
  intro r hr
  apply mem_centralizer_iff.mpr
  intro j hj
  have he := congrArg (fun b : MulAut Matrix.PSL3Two.SL => b (f ⟨j,hj⟩))
    (htriv ⟨r,hr⟩)
  rw [ha] at he
  have hfix := congrArg Subtype.val (f.injective he)
  change r * j * r⁻¹ = j at hfix
  exact ((mul_inv_eq_iff_eq_mul).mp hfix).symm

private theorem CubicLinearAction_goldschmidt_linear_component_residual
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B) (J : Subgroup D) [J.Normal]
    [Group.IsPerfect J] (e : J ≃* Matrix.PSL3Two.PSL)
    (hcases : ((pResidual 2 A).map A.subtype ≤ J ∧ J ⊔ B = ⊤) ∨
      ((pResidual 2 B).map B.subtype ≤ J ∧ J ⊔ A = ⊤))
    (hout : ¬ (pResidual 2 B).map B.subtype ≤
      normalizer ((pResidual 2 A).map A.subtype : Set D)) :
    (pResidual 2 A).map A.subtype ≤ J ∧
      (pResidual 2 B).map B.subtype ≤ J ∧ pResidual 2 D = J := by
  have hboth : (pResidual 2 A).map A.subtype ≤ J ∧
      (pResidual 2 B).map B.subtype ≤ J := by
    rcases hcases with ⟨hA,_⟩ | ⟨hB,_⟩
    · refine ⟨hA,?_⟩
      by_contra hn
      exact hout (((CubicLinearAction_goldschmidt_escaping_residual_centralizes_linear ht J e hn).trans
        (centralizer_le hA)).trans (Subgroup.centralizer_le_normalizer _))
    · refine ⟨?_,hB⟩
      by_contra hn
      have hc := CubicLinearAction_goldschmidt_escaping_residual_centralizes_linear ht.symm J e hn
      exact hout ((hB.trans (le_centralizer_iff.mp hc)).trans (Subgroup.centralizer_le_normalizer _))
  refine ⟨hboth.1,hboth.2,le_antisymm ?_ ?_⟩
  · rw [ht.twoResidual_eq_sup]
    exact sup_le hboth.1 hboth.2
  · apply le_pResidual_of_isPPerfect J
    intro N hN hq
    let : N.Normal := hN
    by_contra hn
    let : Nontrivial (J ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
    let : Group.IsPerfect (J ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (J ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (J ⧸ N) inferInstance


private theorem CubicLinearAction_goldschmidt_linear_residual_eq_top
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B) (hcore : pCore 2 D = ⊥)
    (J : Subgroup D) [J.Normal] [Group.IsPerfect J] [IsSimpleGroup J]
    (e : J ≃* Matrix.PSL3Two.PSL) (hres : pResidual 2 D = J) : J = ⊤ := by
  let : Group.IsSolvable A := SymmetricThreeTwoCore.solvable ht.quotient_left.some
  have hquot : IsPGroup 2 (D ⧸ J) := hres ▸ isPGroup_quotient_pResidual 2
  have hC : centralizer (J : Set D) = ⊥ := centralizer_eq_bot_of_simple_two_quotient
    J (Group.IsPerfect.not_isMulCommutative J) hquot hcore
  obtain ⟨S,hS⟩ := ht.intersection_sylow
  have hSA : (S : Subgroup D) ≤ A := hS.symm.le.trans inf_le_left
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal J
  let P := A.subgroupOf J
  have hRP : (R : Subgroup J) ≤ P := by rw [hR]; exact comap_mono hSA
  have hproper : P ≠ ⊤ := by
    intro hz
    have hJA : J ≤ A := subgroupOf_eq_top.mp hz
    exact Group.IsPerfect.not_isSolvable J
      (Group.isSolvable_of_isSolvable_injective (f := inclusion hJA) (inclusion_injective hJA))
  have hRA : (pResidual 2 A).map A.subtype ≤ J := hres ▸ map_pResidual_le 2 A.subtype
  have hnot : ¬ IsPGroup 2 P := by
    intro hp
    have hp' : IsPGroup 2 (A ⊓ J : Subgroup D) :=
      (subgroupOf_map_subtype A J) ▸ hp.map J.subtype
    have hle : A ⊓ J ≤ (pCore 2 A).map A.subtype :=
      le_pCoreIn_of_normalizes hp' inf_le_left
        ((le_inf A.le_normalizer le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf)
    exact ((ht.left_subnormal_core_iff_not_residual_le J
      (Normal.isSubnormal inferInstance)).mp hle) hRA
  obtain ⟨f,_,hP⟩ := Matrix.PSL3Two.exists_sylow_line_marking e R P hRP hproper hnot
  have hSJ : (S : Subgroup D) ≤ J := by
    intro s hs
    let a : MulAut J := MulAut.conjNormal s
    have hPa : P.map a.toMonoidHom = P := by
      apply eq_of_le_of_card_ge
      · rintro x ⟨x,hx,rfl⟩
        change s * (x : D) * s⁻¹ ∈ A
        exact A.mul_mem (A.mul_mem (hSA hs) hx) (A.inv_mem (hSA hs))
      · rw [card_map_of_injective (f := a.toMonoidHom) a.injective]
    let b := MulAut.congr f a
    have hb : Matrix.PSL3Two.lineParabolicSL.map b.toMonoidHom = Matrix.PSL3Two.lineParabolicSL := by
      have he : b.toMonoidHom.comp f.toMonoidHom = f.toMonoidHom.comp a.toMonoidHom := by
        apply MonoidHom.ext
        intro x
        change f (a (f.symm (f x))) = f (a x)
        rw [f.symm_apply_apply]
      rw [←hP,map_map,he,←map_map,hPa]
    have hbR : (Matrix.PSL3Two.MarkedAutomorphisms.residual Matrix.PSL3Two.lineParabolicSL).map
        b.toMonoidHom = Matrix.PSL3Two.MarkedAutomorphisms.residual Matrix.PSL3Two.lineParabolicSL := by
      change ((pResidual 2 Matrix.PSL3Two.lineParabolicSL).map
        Matrix.PSL3Two.lineParabolicSL.subtype).map b.toMonoidHom = _
      rw [map_embedded_pResidual,hb]
      rfl
    obtain ⟨g,_,hg⟩ := Matrix.PSL3Two.MarkedAutomorphisms.preserving_residual_is_conj
      _ (Or.inr rfl) b hbR
    let j := f.symm g
    have ha : a = MulAut.conj j := by
      apply MulEquiv.ext
      intro x
      apply f.injective
      have hh := congrArg (fun c : MulAut Matrix.PSL3Two.SL => c (f x)) hg
      change f (a (f.symm (f x))) = g * f x * g⁻¹ at hh
      rw [f.symm_apply_apply] at hh
      change f (a x) = f (j * x * j⁻¹)
      simpa only [map_mul,map_inv,j,f.apply_symm_apply] using hh
    have hsj : s * (j : D)⁻¹ ∈ centralizer (J : Set D) := by
      rw [←MulAut.conjNormal_ker_eq_centralizer J]
      change (MulAut.conjNormal : D →* MulAut J) (s * (j : D)⁻¹) = 1
      rw [map_mul,map_inv,MulAut.conjNormal_val]
      change a * (MulAut.conj j)⁻¹ = 1
      rw [ha,mul_inv_cancel]
    have he : s = (j : D) := mul_inv_eq_one.mp (mem_bot.mp (hC ▸ hsj))
    exact he.symm ▸ j.property
  have hh := pResidual_sup_sylow_eq_top S
  rw [hres,sup_eq_left.mpr hSJ] at hh
  exact hh


/-- A core-free Goldschmidt completion with a normal linear-three component
and nonnormalizing cubic residuals is exactly that component. -/
theorem goldschmidt_linear_completion
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B) (hcore : pCore 2 D = ⊥)
    (J : Subgroup D) [J.Normal] [Group.IsPerfect J] [IsSimpleGroup J]
    (e : J ≃* Matrix.PSL3Two.PSL)
    (hcases : ((pResidual 2 A).map A.subtype ≤ J ∧ J ⊔ B = ⊤) ∨
      ((pResidual 2 B).map B.subtype ≤ J ∧ J ⊔ A = ⊤))
    (hout : ¬ (pResidual 2 B).map B.subtype ≤
      normalizer ((pResidual 2 A).map A.subtype : Set D)) : J = ⊤ := by
  exact CubicLinearAction_goldschmidt_linear_residual_eq_top ht hcore J e
    (CubicLinearAction_goldschmidt_linear_component_residual ht J e hcases hout).2.2


open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The A₅ component alternative is impossible in the original cubic
completion: its faithful image would have a normal Sylow four-group. -/
theorem cubic_generated_component_not_alternating_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    ¬ Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  obtain ⟨_,⟨e⟩⟩ := cubic_generated_component_action_kernel_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨_,_,hnq,_⟩ := cubic_generated_component_action_reduction_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  let : (J.map q).Normal := hnq
  obtain ⟨_,ht,hcore⟩ := cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he
  rintro ⟨a⟩
  exact CubicLinearAction_goldschmidt_no_alternating_normal ht hcore (J.map q) (e.symm.trans a)

/-- The original full point-normality interface. -/
theorem cubic_generated_component_not_alternating
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    ¬ Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) := by
  apply cubic_generated_component_not_alternating_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- Every C-component of the original escaping cubic completion has the
actual PSL₃(2) two-core quotient. The earlier A₅ alternative is discharged. -/
theorem cubic_generated_component_linear_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  obtain ⟨hJL,hJf⟩ := cubic_generated_component_faithful_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he J hJ
  let eJ := J.equivMapOfInjective D.subtype D.subtype_injective
  let eQ := QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)
  rcases (faithful (J.map D.subtype) hJL hJf).1 with a | a
  · exact (cubic_generated_component_not_alternating_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ ⟨eQ.trans a.some⟩).elim
  · exact ⟨eQ.trans a.some⟩

/-- The original full point-normality interface. -/
theorem cubic_generated_component_linear
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL) := by
  apply cubic_generated_component_linear_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- Both original cubic residuals lie in the component image. They generate
the entire two-residual of the literal action quotient, isomorphic to PSL₃(2). -/
theorem cubic_generated_component_action_residual_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    J.Normal ∧ (q.subgroupMap J).ker = pCore 2 J ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL) ∧
      pResidual 2 (D ⧸ C) = J.map q ∧
      ((F.Li L 2).subgroupOf D).map q ⊔ (Y.subgroupOf D).map q = J.map q ∧
      Nonempty ((pResidual 2 (D ⧸ C)) ≃* Matrix.PSL3Two.PSL) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  obtain ⟨a⟩ := cubic_generated_component_linear_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨hk,⟨e⟩⟩ := cubic_generated_component_action_kernel_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨hnJ,hjq,hnq,hcases⟩ := cubic_generated_component_action_reduction_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  let : (J.map q).Normal := hnq
  let : IsQuasisimple (J.map q) := hjq.2
  obtain ⟨_,ht,_⟩ := cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he
  have ho := cubic_generated_action_normalizer_obstruction_of_normalizes_point h structural Y hYH hYL hout
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  have ha : (pResidual 2 (((F.P L).subgroupOf D).map q)).map
      (((F.P L).subgroupOf D).map q).subtype = ((F.Li L 2).subgroupOf D).map q := by
    rw [←map_embedded_pResidual,hr.1]
  have hb : (pResidual 2 (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q)).map
      (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q).subtype = (Y.subgroupOf D).map q := by
    rw [←map_embedded_pResidual,hr.2]
  have hh := CubicLinearAction_goldschmidt_linear_component_residual ht (J.map q) (e.symm.trans a)
    (by rwa [ha,hb]) (by rwa [ha,hb])
  have hgen : ((F.Li L 2).subgroupOf D).map q ⊔ (Y.subgroupOf D).map q = J.map q := by
    rw [←ha,←hb,←ht.twoResidual_eq_sup]
    exact hh.2.2
  exact ⟨hnJ,hk,⟨a⟩,hh.2.2,hgen,
    ⟨(MulEquiv.subgroupCongr hh.2.2).trans (e.symm.trans a)⟩⟩

/-- The original full point-normality interface. -/
theorem cubic_generated_component_action_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    J.Normal ∧ (q.subgroupMap J).ker = pCore 2 J ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL) ∧
      pResidual 2 (D ⧸ C) = J.map q ∧
      ((F.Li L 2).subgroupOf D).map q ⊔ (Y.subgroupOf D).map q = J.map q ∧
      Nonempty ((pResidual 2 (D ⧸ C)) ≃* Matrix.PSL3Two.PSL) := by
  apply cubic_generated_component_action_residual_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The entire faithful action quotient of the nonsolvable cubic completion
is PSL₃(2); the parabolic preserved by the original Sylow excludes outer action. -/
theorem cubic_generated_component_action_quotient_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    Nonempty ((D ⧸ C) ≃* Matrix.PSL3Two.PSL) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  obtain ⟨_,_,⟨a⟩,hr,_,_⟩ := cubic_generated_component_action_residual_of_normalizes_point
    h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨_,⟨e⟩⟩ := cubic_generated_component_action_kernel_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨_,hj,hnj,_⟩ := cubic_generated_component_action_reduction_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  let : (J.map q).Normal := hnj
  let : IsQuasisimple (J.map q) := hj.2
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup (J.map q) := (e.symm.trans a).isSimpleGroup
  obtain ⟨_,ht,hcore⟩ := cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he
  have hjtop := CubicLinearAction_goldschmidt_linear_residual_eq_top ht hcore (J.map q) (e.symm.trans a) hr
  exact ⟨Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hjtop.symm).trans (e.symm.trans a))⟩

/-- The original full point-normality interface. -/
theorem cubic_generated_component_action_quotient
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    Nonempty ((D ⧸ C) ≃* Matrix.PSL3Two.PSL) := by
  apply cubic_generated_component_action_quotient_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04 in
/-- For the literal order-four chief interval, a nonsolvable cubic completion
has a normal faithful PSL₃(2) component whose image is the entire
faithful action quotient. The original star kernel and both cubic generators are retained. -/
theorem extraspecial_four_interval_cubic_linear_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 ∧
      Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      let W := conjugateSpanBy (F.Vi 1) D
      letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy _ _)
      let C := centralizer (W.subgroupOf D : Set D)
      let q := QuotientGroup.mk' C
      Group.IsSolvable D ∨ ∃ J : Subgroup G, ∃ _hJD : J ≤ D,
        (J.subgroupOf D).IsCComponent ∧ (J.subgroupOf D).Normal ∧
        J ∈ Chapter1.LStar G (T : Subgroup G) ∧ IsFaithfulSignalizerType J ∧
        (J.subgroupOf (J ⊔ (T : Subgroup G))).Normal ∧
        Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL) ∧
        (q.subgroupMap (J.subgroupOf D)).ker = pCore 2 (J.subgroupOf D) ∧
        Nonempty ((J ⧸ pCore 2 J) ≃* (J.subgroupOf D).map q) ∧
        pResidual 2 (D ⧸ C) = (J.subgroupOf D).map q ∧
        ((F.Li L 2).subgroupOf D).map q ⊔ (Y.subgroupOf D).map q = (J.subgroupOf D).map q ∧
        Nonempty ((pResidual 2 (D ⧸ C)) ≃* Matrix.PSL3Two.PSL) ∧
        Nonempty ((D ⧸ C) ≃* Matrix.PSL3Two.PSL) := by
  classical
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he⟩ :=
    extraspecial_four_interval_escaping_symmetricThree h hab structural previous hex hcard hexp
      N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  refine ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,?_⟩
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  by_cases hs : Group.IsSolvable D
  · exact Or.inl hs
  right
  obtain ⟨J,hJD,hJ,hmax,hf,hnJ,_⟩ := cubic_generated_nonsolvable_component
    h hab structural previous faithful hn Y hYH hYp hYT hout he hs
  obtain ⟨hnD,hk,⟨a⟩,hres,hgen,hmodel⟩ := cubic_generated_component_action_residual
    h hab structural previous faithful hn Y hYH hYp hYT hout he (J.subgroupOf D) hJ
  obtain ⟨_,⟨e⟩⟩ := cubic_generated_component_action_kernel h hab structural previous faithful hn
    Y hYH hYp hYT hout he (J.subgroupOf D) hJ
  let eJ := subgroupOfEquivOfLe hJD
  let eQ := QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)
  exact ⟨J,hJD,hJ,hnD,hmax,hf,hnJ,⟨eQ.symm.trans a⟩,hk,⟨eQ.symm.trans e⟩,hres,hgen,hmodel,
    cubic_generated_component_action_quotient h hab structural previous faithful hn
      Y hYH hYp hYT hout he (J.subgroupOf D) hJ⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end


/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Natural geometry of the nonsolvable cubic completion

The proved faithful quotient D/C_D(W) is marked at both original cubic
vertices: P maps to the line parabolic and YT to the point parabolic.
Conjugation on the literal elementary subgroup W = ⟨V₁ᴰ⟩ descends through
this quotient. The point is fixed by YT and its P-span is exactly V₂,
so H.5.5 gives actual equivariant natural coordinates on W.

In particular |W| = 8. Since an escaping Y cannot normalize V₂, its
V₂-span is larger than the plane and hence equals W. Thus W ≤ U and
⟨Wᴴ⟩ = U. Natural transitivity and this abelian span imply that intersecting
conjugates of W commute. This supplies the symmetric abelian geometry
needed in the remaining ambient exclusion, without an additional 14.4.14
premise. The last theorem applies all these deductions to the actual
order-four chief interval, retaining the original star kernel and cubic.

The ambient critical-pair exclusion of this nonsolvable case, solvability
of D, and the later containment and residual classification are still needed.
EarlierFaithfulClassification is the independent 14.3.4 input, with its
existing producer and final discharge at the original source parents.

Source: Aschbacher–Smith, H.5.5, printed p.386; proof of 14.5.8,
printed pp.1014–1015; its use in 14.7.20, printed p.1049,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
universe u

private theorem CubicNaturalModule_goldschmidt_linear_marking
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B) (e : D ≃* Matrix.PSL3Two.PSL) :
    ∃ f : D ≃* Matrix.PSL3Two.SL,
      A.map f.toMonoidHom = Matrix.PSL3Two.lineParabolicSL ∧
      B.map f.toMonoidHom = Matrix.PSL3Two.pointParabolicSL := by
  let : Group.IsSolvable A := SymmetricThreeTwoCore.solvable ht.quotient_left.some
  let : Group.IsSolvable B := SymmetricThreeTwoCore.solvable ht.quotient_right.some
  have hns : ¬ Group.IsSolvable D := by
    intro hs
    let := hs
    exact not_isSolvable_psl3_two
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  have hproper (P : Subgroup D) [Group.IsSolvable P] : P ≠ ⊤ := by
    intro he
    have hp : Function.Surjective P.subtype := by
      intro x
      exact ⟨⟨x,he ▸ mem_top x⟩,rfl⟩
    exact hns (Group.isSolvable_of_surjective (f := P.subtype) hp)
  obtain ⟨S,hS⟩ := ht.intersection_sylow
  have hSA : (S : Subgroup D) ≤ A := hS.symm.le.trans inf_le_left
  have hSB : (S : Subgroup D) ≤ B := hS.symm.le.trans inf_le_right
  have hnot (P : Subgroup D) (hSP : (S : Subgroup D) ≤ P)
      (he : Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))) : ¬ IsPGroup 2 P := by
    intro hp
    have hPS := S.is_maximal' hp hSP
    have hi := SymmetricThreeTwoCore.sylow_index_three he.some (S.subtype hSP)
    change (S : Subgroup D).relIndex P = 3 at hi
    rw [hPS,relIndex_self] at hi
    omega
  obtain ⟨f,hSf,hAf⟩ := Matrix.PSL3Two.exists_sylow_line_marking e S A hSA
    (hproper A) (hnot A hSA ht.quotient_left)
  have hBf : B.map f.toMonoidHom = Matrix.PSL3Two.pointParabolicSL := by
    have hBP : B.map f.toMonoidHom ≠ ⊤ := by
      intro hz
      apply hproper B
      exact f.mapSubgroup.injective (hz.trans f.mapSubgroup.map_top.symm)
    have hBtwo : ¬ IsPGroup 2 (B.map f.toMonoidHom) := fun hh =>
      hnot B hSB ht.quotient_right (hh.of_equiv (f.subgroupMap B).symm)
    rcases Matrix.PSL3Two.parabolic_of_borel_le_of_not_two _
      (hSf ▸ map_mono hSB) hBP hBtwo with hh | hh
    · exact hh
    · have heq : A = B := f.mapSubgroup.injective (hAf.trans hh.symm)
      have hAtop : A = ⊤ := by simpa only [←heq,sup_idem] using ht.generated
      exact (hproper A hAtop).elim
  exact ⟨f,hAf,hBf⟩

open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The surviving nonsolvable action has natural coordinates on the literal
point span. One quotient marking identifies both original vertices, and the
coordinates intertwine the original ambient conjugation. -/
theorem cubic_generated_component_natural_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    ∃ (e : (D ⧸ C) ≃* Matrix.PSL3Two.SL)
      (f : W ≃* Multiplicative BinaryLinearThree.Vector),
      (((F.P L).subgroupOf D).map q).map e.toMonoidHom = Matrix.PSL3Two.lineParabolicSL ∧
      (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q).map e.toMonoidHom =
        Matrix.PSL3Two.pointParabolicSL ∧
      ∀ (g : D) (w : W),
        (f (W.normalizerMonoidHom
          (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) w)).toAdd =
          BinaryLinearThree.W (e (q g)) (f w).toAdd := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  obtain ⟨e₀⟩ := cubic_generated_component_action_quotient_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨_,ht,_⟩ := cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he
  obtain ⟨e,hA,hB⟩ := CubicNaturalModule_goldschmidt_linear_marking ht e₀
  let π := e.toMonoidHom.comp q
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective C)
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hZD : F.Vi 1 ≤ D := (F.le_seed 1).trans (h.chosen.le_sylow.trans hTD)
  have hWD : W ≤ D := conjugateSpanBy_le_self hZD
  let : IsElementaryAbelian 2 W :=
    (cubic_generated_local_structure h hab structural previous Y hYH he).2.2.1
  have hker : π.ker ≤ (centralizer (W : Set G)).subgroupOf D := by
    intro g hg
    have hq : q g = 1 := e.injective (show e (q g) = e 1 from hg.trans e.map_one.symm)
    have hgC : g ∈ C := (QuotientGroup.eq_one_iff g).mp hq
    apply mem_centralizer_iff.mpr
    intro w hw
    have hc := mem_centralizer_iff.mp hgC (⟨w,hWD hw⟩ : D) hw
    exact congrArg Subtype.val hc
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  let := h.chosen.elementary
  obtain ⟨z,hz1,hZ⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hplane : conjugateSpanBy (F.Vi 1) (F.P L) = F.Vi 2 := by
    apply le_antisymm
    · exact conjugateSpanBy_le (F.monotone (by decide : 1 ≤ 2))
        (F.P_le_G₂ (by decide) L h.chosen.normalizes)
    · rw [←plane_eq_point_residual_span h structural]
      apply conjugateSpanBy_mono le_rfl
      rw [plane_parabolic_eq_join h structural]
      exact le_sup_left
  have hBZ : Y ⊔ (T : Subgroup G) ≤ centralizer (F.Vi 1 : Set G) :=
    (sup_le hYH (F.invariant 1)).trans (normalizer_le_centralizer_of_card_two _ hc)
  obtain ⟨f,hf⟩ := Representation.ConjugatePointNatural.exists_natural_coordinates
    D W (F.Vi 1) (F.P L) (Y ⊔ (T : Subgroup G))
    (le_normalizer_conjugateSpanBy _ _) (le_conjugateSpanBy _ _) z hZ hz1
    π hπ hker le_sup_left (by rwa [←map_map]) (by rwa [←map_map]) hBZ rfl
    (by rw [hplane]; simpa using F.card 2 (by decide))
  exact ⟨e,f,hA,hB,hf⟩

/-- The original full point-normality interface. -/
theorem cubic_generated_component_natural
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    ∃ (e : (D ⧸ C) ≃* Matrix.PSL3Two.SL)
      (f : W ≃* Multiplicative BinaryLinearThree.Vector),
      (((F.P L).subgroupOf D).map q).map e.toMonoidHom = Matrix.PSL3Two.lineParabolicSL ∧
      (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q).map e.toMonoidHom =
        Matrix.PSL3Two.pointParabolicSL ∧
      ∀ (g : D) (w : W),
        (f (W.normalizerMonoidHom
          (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) w)).toAdd =
          BinaryLinearThree.W (e (q g)) (f w).toAdd := by
  apply cubic_generated_component_natural_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- In the nonsolvable branch the natural point span is exactly the
Y-span of the original plane. Its full point-normalizer span is the same
original abelian U, so intersecting conjugates of this new seed commute. -/
theorem cubic_generated_component_span_geometry_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    Nat.card W = 8 ∧ W = conjugateSpanBy (F.Vi 2) Y ∧
      W ≤ F.U ∧ conjugateSpanBy W F.H = F.U ∧
      IsMulCommutative (conjugateSpanBy W F.H) ∧
      ∀ g : G, W ⊓ W.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
        ⁅W,W.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  let := h.chosen.elementary
  let := hab
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  obtain ⟨e,f,_,_,hf⟩ := cubic_generated_component_natural_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  have hW8 : Nat.card W = 8 := by
    rw [Nat.card_congr f.toEquiv]
    change Nat.card (Fin 3 → ZMod 2) = 8
    norm_num [Nat.card_fun]
  have hYD : Y ≤ D := le_sup_left.trans le_sup_right
  have hPW : F.Vi 2 ≤ W := by
    rw [←plane_eq_point_residual_span h structural]
    apply conjugateSpanBy_mono le_rfl
    change F.Li L 2 ≤ F.P L ⊔ (Y ⊔ (T : Subgroup G))
    rw [plane_parabolic_eq_join h structural]
    exact le_sup_left.trans le_sup_left
  let S := conjugateSpanBy (F.Vi 2) Y
  have hSW : S ≤ W := conjugateSpanBy_le hPW
    (hYD.trans (le_normalizer_conjugateSpanBy _ _))
  have h4 : 4 ≤ Nat.card S := by
    simpa only [F.card 2 (by decide), show (2 : ℕ) ^ 2 = 4 from rfl] using
      card_le_of_le (le_conjugateSpanBy (F.Vi 2) Y)
  have hn4 : Nat.card S ≠ 4 := by
    intro hc
    have hPS : F.Vi 2 = S := eq_of_le_of_card_ge (le_conjugateSpanBy _ _)
      (by rw [hc,F.card 2 (by decide)]; rfl)
    apply hout
    apply point_plane_normalizer_le h structural Y hYL
    rw [hPS]
    exact le_normalizer_conjugateSpanBy _ _
  have hS8 : Nat.card S = 8 := by
    have hd : Nat.card S ∣ 8 := hW8 ▸ card_dvd_of_le hSW
    have hm : Nat.card S ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hd,by decide⟩
    have heq : Nat.divisors 8 = {1,2,4,8} := by decide
    rw [heq] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    omega
  have hWS : W = S := (eq_of_le_of_card_ge hSW (by rw [hW8,hS8])).symm
  have hWU : W ≤ F.U := by
    rw [hWS]
    exact conjugateSpanBy_le ((F.le_seed 2).trans (le_conjugateSpanBy _ _))
      (hYH.trans (le_normalizer_conjugateSpanBy _ _))
  let := F.localKernel_tilde_seed_elementary
  have hspan : conjugateSpanBy W F.H = F.U := by
    apply le_antisymm
    · exact conjugateSpanBy_le hWU (le_normalizer_conjugateSpanBy _ _)
    · rw [F.U_eq_plane_span L (by decide) h.chosen.normalizes
        (F.invariant_subgroup_of_ambient_natural h.naturalMarking (by decide))]
      exact conjugateSpanBy_mono hPW le_rfl
  have habW : IsMulCommutative (conjugateSpanBy W F.H) := hspan.symm ▸ hab
  refine ⟨hW8,hWS,hWU,hspan,habW,?_⟩
  obtain ⟨z,hz1,hZ⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hzW : z ∈ W := le_conjugateSpanBy _ _ (hZ ▸ mem_zpowers z)
  have htrans : ∀ x ∈ W, x ≠ 1 → ∃ n ∈ normalizer (W : Set G),
      (MulAut.conj n) z = x := by
    intro x hx hx1
    let zW : W := ⟨z,hzW⟩
    let xW : W := ⟨x,hx⟩
    have hzn : (f zW).toAdd ≠ 0 := by
      intro hh
      have hfz : f zW = 1 := hh
      exact hz1 (congrArg Subtype.val (f.injective (hfz.trans f.map_one.symm)))
    have hxn : (f xW).toAdd ≠ 0 := by
      intro hh
      have hfx : f xW = 1 := hh
      exact hx1 (congrArg Subtype.val (f.injective (hfx.trans f.map_one.symm)))
    obtain ⟨a,ha⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three _ _ hzn hxn
    obtain ⟨g,hg⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective C)) a
    refine ⟨g,(le_normalizer_conjugateSpanBy _ _) g.property,?_⟩
    have hh := hf g zW
    change e (q g) = a at hg
    change (f (W.normalizerMonoidHom
      (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) zW)).toAdd =
        BinaryLinearThree.W (e (q g)) (f zW).toAdd at hh
    rw [hg] at hh
    have hfx : f (W.normalizerMonoidHom
        (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) zW) = f xW :=
      Multiplicative.toAdd.injective (hh.trans ha)
    exact congrArg Subtype.val (f.injective hfx)
  have hc := (point_span_abelian_iff_intersecting_conjugates_commute W hzW hz1 htrans).mp
    (show IsMulCommutative (conjugateSpanBy W (centralizer ({z} : Set G))) from
      (F.H_eq_centralizer (by decide) z hZ) ▸ habW)
  exact hc

/-- The original full point-normality interface. -/
theorem cubic_generated_component_span_geometry
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    Nat.card W = 8 ∧ W = conjugateSpanBy (F.Vi 2) Y ∧
      W ≤ F.U ∧ conjugateSpanBy W F.H = F.U ∧
      IsMulCommutative (conjugateSpanBy W F.H) ∧
      ∀ g : G, W ⊓ W.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
        ⁅W,W.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  apply cubic_generated_component_span_geometry_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04 in
/-- The literal order-four chief interval supplies all inputs to natural
recognition. In the nonsolvable branch both vertices are marked and the
actual point span has the same abelian point-normalizer span as V. -/
theorem extraspecial_four_interval_cubic_natural
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 ∧
      Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      let W := conjugateSpanBy (F.Vi 1) D
      letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy _ _)
      let C := centralizer (W.subgroupOf D : Set D)
      let q := QuotientGroup.mk' C
      Group.IsSolvable D ∨
        Nat.card W = 8 ∧ W = conjugateSpanBy (F.Vi 2) Y ∧
        W ≤ F.U ∧ conjugateSpanBy W F.H = F.U ∧
        (∀ g : G, W ⊓ W.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
          ⁅W,W.map (MulAut.conj g).toMonoidHom⁆ = ⊥) ∧
        ∃ (e : (D ⧸ C) ≃* Matrix.PSL3Two.SL)
          (f : W ≃* Multiplicative BinaryLinearThree.Vector),
          (((F.P L).subgroupOf D).map q).map e.toMonoidHom = Matrix.PSL3Two.lineParabolicSL ∧
          (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q).map e.toMonoidHom =
            Matrix.PSL3Two.pointParabolicSL ∧
          ∀ (g : D) (w : W),
            (f (W.normalizerMonoidHom
              (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) w)).toAdd =
              BinaryLinearThree.W (e (q g)) (f w).toAdd := by
  classical
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he⟩ :=
    extraspecial_four_interval_escaping_symmetricThree h hab structural previous hex hcard hexp
      N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  refine ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,?_⟩
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  by_cases hs : Group.IsSolvable D
  · exact Or.inl hs
  right
  obtain ⟨J,hJD,hJ,_⟩ := cubic_generated_nonsolvable_component
    h hab structural previous faithful hn Y hYH hYp hYT hout he hs
  obtain ⟨hcW,hWY,hWU,hspan,_,hcomm⟩ := cubic_generated_component_span_geometry
    h hab structural previous faithful hn Y hYH hYp hYT hout he (J.subgroupOf D) hJ
  exact ⟨hcW,hWY,hWU,hspan,hcomm,cubic_generated_component_natural
    h hab structural previous faithful hn Y hYH hYp hYT hout he (J.subgroupOf D) hJ⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# The full cubic quotient and its literal overlap

In the nonsolvable cubic branch, the component image in D/O₂(D) is again
PSL₃(2). The Goldschmidt reduction and the nonnormalizing cubic residuals
force it to be the entire quotient. Comparing this with D/C_D(W) proves
C_D(W) = O₂(D), preserving the original quotient kernel.

The natural point span W and the original seed V both have order eight.
They contain V₂ and are distinct, since equality would make Y normalize V.
Thus V ∩ W = V₂. Their common normalizers give LT ∩ D = P, with exactly
the original plane parabolic, as required by the subsequent coset geometry.

Source: Aschbacher–Smith, proof of 14.5.8, printed pp.1014–1015,
refs/quasithin.pdf. The ambient exclusion is assembled in the next module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
/-- The literal two-core quotient is the linear-three group. -/
theorem cubic_generated_component_core_quotient_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    Nonempty ((D ⧸ pCore 2 D) ≃* Matrix.PSL3Two.PSL) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let Q := pCore 2 D
  let q := QuotientGroup.mk' Q
  let qC := QuotientGroup.mk' C
  have ht := cubic_goldschmidt_triple h structural Y hYH he
  have hQC : Q ≤ C := (cubic_generated_action_kernel_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he).1.symm.le.trans inf_le_right
  let r : (D ⧸ Q) →* (D ⧸ C) := QuotientGroup.map Q C (MonoidHom.id D) hQC
  have hcomp : r.comp q = qC := by
    ext x
    rfl
  have hk : (q.subgroupMap J).ker = pCore 2 J := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hJ.subnormal).symm
  let eJ : (J ⧸ pCore 2 J) ≃* J.map q :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (q.subgroupMap_surjective J))
  obtain ⟨e₀⟩ := cubic_generated_component_linear_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  let e := eJ.symm.trans e₀
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup (J.map q) := e.isSimpleGroup
  let := hJ.perfect
  let : Group.IsPerfect (J.map q) := Group.IsPerfect.map q
  have hz : center (J.map q) = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (J.map q)) inferInstance).resolve_right
      (fun hh => Group.IsPerfect.not_isMulCommutative (J.map q) (center_eq_top_iff.mp hh))
  let : IsQuasisimple (J.map q) := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hj : IsComponent (D ⧸ Q) (J.map q) :=
    ⟨hJ.subnormal.map (QuotientGroup.mk'_surjective Q),inferInstance⟩
  have hSQ := (cubic_generated_local_structure h hab structural previous Y hYH he).2.1
  obtain ⟨hJn,hcases⟩ := ChapterF.SourceAssembly.source_component_reduction
    (ChapterA.Section02.theoremA_knownSimple (G := D)) hSQ q (QuotientGroup.mk'_surjective Q)
    ht.quotient_twoCore ht.quotient_twoCore_eq_bot hj
  let : (J.map q).Normal := hJn
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  have hnot : ¬ (pResidual 2 (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q)).map
      (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q).subtype ≤
      normalizer ((pResidual 2 (((F.P L).subgroupOf D).map q)).map
        (((F.P L).subgroupOf D).map q).subtype : Set (D ⧸ Q)) := by
    rw [←map_embedded_pResidual,←map_embedded_pResidual,hr.1,hr.2]
    intro hh
    have hm := (map_mono (f := r) hh).trans (le_normalizer_map r)
    rw [map_map,map_map,hcomp] at hm
    exact cubic_generated_action_normalizer_obstruction_of_normalizes_point h structural Y hYH hYL hout hm
  have htop := goldschmidt_linear_completion ht.quotient_twoCore
    ht.quotient_twoCore_eq_bot (J.map q) e hcases hnot
  exact ⟨topEquiv.symm.trans ((MulEquiv.subgroupCongr htop.symm).trans e)⟩

/-- The original full point-normality interface. -/
theorem cubic_generated_component_core_quotient
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    Nonempty ((D ⧸ pCore 2 D) ≃* Matrix.PSL3Two.PSL) := by
  apply cubic_generated_component_core_quotient_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The point-span action has exactly the full two-core as kernel. -/
theorem cubic_generated_component_kernel_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    centralizer (W.subgroupOf D : Set D) = pCore 2 D := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let Q := pCore 2 D
  have hQC : Q ≤ C := (cubic_generated_action_kernel_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he).1.symm.le.trans inf_le_right
  obtain ⟨eQ⟩ := cubic_generated_component_core_quotient_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨eC⟩ := cubic_generated_component_action_quotient_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  let r : (D ⧸ Q) →* (D ⧸ C) := QuotientGroup.map Q C (MonoidHom.id D) hQC
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective C x
    exact ⟨QuotientGroup.mk' Q g,rfl⟩
  have hc : Nat.card (D ⧸ C) = Nat.card (D ⧸ Q) := Nat.card_congr (eC.trans eQ.symm).toEquiv
  have hi := (hr.bijective_of_nat_card_le hc.ge).injective
  apply le_antisymm _ hQC
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply hi
  change QuotientGroup.mk' C x = r 1
  rw [r.map_one]
  exact (QuotientGroup.eq_one_iff x).mpr hx

/-- The original full point-normality interface. -/
theorem cubic_generated_component_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    centralizer (W.subgroupOf D : Set D) = pCore 2 D := by
  apply cubic_generated_component_kernel_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The two rank-three seeds meet in the original plane. -/
theorem cubic_generated_component_seed_intersection_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    V ⊓ W = F.Vi 2 := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  obtain ⟨hW8,hWY,_,_⟩ := cubic_generated_component_span_geometry_of_normalizes_point
    h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  change Nat.card W = 8 at hW8
  change W = conjugateSpanBy (F.Vi 2) Y at hWY
  have hPW : F.Vi 2 ≤ W := by
    rw [hWY]
    exact le_conjugateSpanBy _ _
  have hle : F.Vi 2 ≤ V ⊓ W := le_inf (F.le_seed 2) hPW
  have h4 : 4 ≤ Nat.card (V ⊓ W : Subgroup G) := by
    simpa only [F.card 2 (by decide), show (2 : ℕ)^2 = 4 from rfl] using card_le_of_le hle
  have hd : Nat.card (V ⊓ W : Subgroup G) ∣ 8 := hW8 ▸ card_dvd_of_le inf_le_right
  have h8 : Nat.card (V ⊓ W : Subgroup G) ≠ 8 := by
    intro hh
    have hIW : V ⊓ W = W := eq_of_le_of_card_ge inf_le_right (by rw [hh,hW8])
    have hWV : W ≤ V := hIW.symm.le.trans inf_le_left
    have hWV' : W = V := eq_of_le_of_card_ge hWV (by rw [hW8,h.seed_card]; rfl)
    have hNV : Y ≤ normalizer (V : Set G) := by
      rw [←hWV']
      exact (le_sup_left.trans le_sup_right : Y ≤ D).trans (le_normalizer_conjugateSpanBy _ _)
    have hu : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
      intro X _ _ hX S M hM
      exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
    exact hout (hNV.trans (h.seed_normalizer_le_at structural))
  have hm : Nat.card (V ⊓ W : Subgroup G) ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hd,by decide⟩
  have heq : Nat.divisors 8 = {1,2,4,8} := by decide
  rw [heq] at hm
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  have hc : Nat.card (V ⊓ W : Subgroup G) = 4 := by omega
  exact (eq_of_le_of_card_ge hle (by rw [hc,F.card 2 (by decide)]; rfl)).symm

/-- The original full point-normality interface. -/
theorem cubic_generated_component_seed_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    V ⊓ W = F.Vi 2 := by
  apply cubic_generated_component_seed_intersection_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The common vertex subgroup is precisely the marked plane parabolic. -/
theorem cubic_generated_component_vertex_intersection_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    (L ⊔ (T : Subgroup G)) ⊓ (F.P L ⊔ (Y ⊔ (T : Subgroup G))) = F.P L := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  have hinter := cubic_generated_component_seed_intersection_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  have hnorm : (L ⊔ (T : Subgroup G)) ⊓ D ≤ normalizer (F.Vi 2 : Set G) := by
    rw [←hinter]
    exact le_normalizer_inf
      (inf_le_left.trans (sup_le h.chosen.normalizes (h.sylow_normalizes_seed_at structural)))
      (inf_le_right.trans (le_normalizer_conjugateSpanBy _ _))
  apply le_antisymm
  · intro x hx
    simp only [InvariantFlag.P,mem_inf,mem_iInf]
    refine ⟨hx.1,?_⟩
    intro i hi
    have hi2 : i = 2 := by omega
    subst i
    exact hnorm hx
  · exact le_inf inf_le_left le_sup_left

/-- The original full point-normality interface. -/
theorem cubic_generated_component_vertex_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    (L ⊔ (T : Subgroup G)) ⊓ (F.P L ⊔ (Y ⊔ (T : Subgroup G))) = F.P L := by
  apply cubic_generated_component_vertex_intersection_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end

/-!
Guarded source extension at the same original G,T. This replays the local
argument with Structural1222At and Theorem12213At; universal exports remain
unchanged. The source reference and mathematical proof are recorded below.

# Solvability of the original escaping cubic completion

Suppose the original cubic Y escapes N_G(L) in the normal-point branch.
A component of D = ⟨P,YT⟩ would give the natural rank-three seed W,
with C_D(W) = O₂(D) and the same abelian point-normalizer span U as V.
Normalizer transitivity and this common span show that intersecting
conjugates commute for the mixed family consisting of both V and W.

Apply the commuting-seed path argument to the literal LT–D coset geometry.
The two local seed centralizers are their two-cores and lie in the common
Sylow T. Thus every conjugate of V under ⟨LT,D⟩ lies in LT and centralizes V.
Its normal span is a nontrivial two-subgroup of O₂(LT), normalized by both
vertices. Uniqueness of the maximal two-local over LT puts its normalizer
in N_G(L), contradicting the original escape of Y. This excludes components
and hence proves D solvable, with no local classification callback.

The final application supplies Y, its exact star kernel and S₃ quotient
from the actual order-four chief interval. The remaining solvable analysis
of 14.5.3(2), small-interval exclusions and 14.7.52 assembly remain open.
EarlierFaithfulClassification retains its existing 14.3.4 producer.

Source: Aschbacher–Smith, 14.5.8, printed pp.1014–1015, and its use
in 14.7.20(2), p.1049, refs/quasithin.pdf. The path induction is the
source's symmetric critical-pair contradiction without choosing its radius.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
/-- Intersecting conjugates commute even when the two seeds have different types. -/
theorem cubic_generated_component_seed_family_commutes_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    let S : Bool → Subgroup G := fun i => if i then W else V
    ∀ i j g k, (S i).conjBy g ⊓ (S j).conjBy k ≠ ⊥ →
      ⁅(S i).conjBy g,(S j).conjBy k⁆ = ⊥ := by
  let := hab
  let := h.chosen.elementary
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let S : Bool → Subgroup G := fun i => if i then W else V
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  obtain ⟨e,f,_,_,hf⟩ := cubic_generated_component_natural_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨_,_,hWU,hspan,_,_⟩ := cubic_generated_component_span_geometry_of_normalizes_point
    h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨z,hz1,hZ⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hzW : z ∈ W := le_conjugateSpanBy _ _ (hZ ▸ mem_zpowers z)
  have hzV : z ∈ V := F.le_seed 1 (hZ ▸ mem_zpowers z)
  have htrans : ∀ i, ∀ x ∈ S i, x ≠ 1 →
      ∃ n ∈ normalizer (S i : Set G), (MulAut.conj n) z = x := by
    intro i x hx hx1
    cases i with
    | false =>
      obtain ⟨l,hl,he⟩ := h.vector_transitive hzV hx hz1 hx1
      exact ⟨l,h.chosen.normalizes hl,he⟩
    | true =>
      let zW : W := ⟨z,hzW⟩
      let xW : W := ⟨x,hx⟩
      have hzn : (f zW).toAdd ≠ 0 := by
        intro hh
        have hfz : f zW = 1 := hh
        exact hz1 (congrArg Subtype.val (f.injective (hfz.trans f.map_one.symm)))
      have hxn : (f xW).toAdd ≠ 0 := by
        intro hh
        have hfx : f xW = 1 := hh
        exact hx1 (congrArg Subtype.val (f.injective (hfx.trans f.map_one.symm)))
      obtain ⟨a,ha⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three _ _ hzn hxn
      obtain ⟨g,hg⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective C)) a
      refine ⟨g,(le_normalizer_conjugateSpanBy _ _) g.property,?_⟩
      have hh := hf g zW
      change e (q g) = a at hg
      change (f (W.normalizerMonoidHom
        (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) zW)).toAdd =
          BinaryLinearThree.W (e (q g)) (f zW).toAdd at hh
      rw [hg] at hh
      have hfx : f (W.normalizerMonoidHom
          (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) zW) = f xW :=
        Multiplicative.toAdd.injective (hh.trans ha)
      exact congrArg Subtype.val (f.injective hfx)
  have hle : ∀ i, S i ≤ F.U := by
    intro i
    cases i
    · exact le_conjugateSpanBy _ _
    · exact hWU
  have hsp : ∀ i, conjugateSpanBy (S i) (centralizer ({z} : Set G)) ≤ F.U := by
    intro i
    rw [←F.H_eq_centralizer (by decide) z hZ]
    cases i
    · exact le_rfl
    · exact hspan.le
  change ∀ (i j : Bool) (g k : G), (S i).conjBy g ⊓ (S j).conjBy k ≠ ⊥ →
    ⁅(S i).conjBy g,(S j).conjBy k⁆ = ⊥
  intro i j g k hi
  exact mixed_conjugates_commute (S i) (S j)
    (mixed_intersection_commutes (S i) (S j) F.U hz1 (hle i) (hsp j) (htrans i) (htrans j))
    g k hi

/-- The original full point-normality interface. -/
theorem cubic_generated_component_seed_family_commutes
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    let S : Bool → Subgroup G := fun i => if i then W else V
    ∀ i j g k, (S i).conjBy g ⊓ (S j).conjBy k ≠ ⊥ →
      ⁅(S i).conjBy g,(S j).conjBy k⁆ = ⊥ := by
  apply cubic_generated_component_seed_family_commutes_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The ambient uniqueness argument excludes every component of D. -/
theorem cubic_generated_no_component_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) : False := by
  let A := L ⊔ (T : Subgroup G)
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let E := A ⊔ D
  let S : Bool → Subgroup G := fun i => if i then W else V
  let M : Bool → Subgroup G := fun i => if i then D else A
  let M₀ := ChapterF.Section07.Geometry.family A D
  let S₀ : Bool → Subgroup E := fun i => (S i).subgroupOf E
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hVD : F.Vi 1 ≤ D := (F.le_seed 1).trans (h.chosen.le_sylow.trans hTD)
  have hSE : ∀ i, S i ≤ E := by
    intro i
    cases i
    · exact h.chosen.le_sylow.trans (le_sup_right.trans le_sup_left)
    · exact (conjugateSpanBy_le_self hVD).trans le_sup_right
  have hSM : ∀ i, S i ≤ M i := by
    intro i
    cases i
    · exact h.chosen.le_sylow.trans le_sup_right
    · exact conjugateSpanBy_le_self hVD
  have hnM : ∀ i, M i ≤ normalizer (S i : Set G) := by
    intro i
    cases i
    · exact sup_le h.chosen.normalizes (h.sylow_normalizes_seed_at structural)
    · exact le_normalizer_conjugateSpanBy _ _
  have hQTA : A.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow A (T.subtype (show (T : Subgroup G) ≤ A from le_sup_right))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ A from le_sup_right)] using hh
  have hQTD : D.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow D (T.subtype hTD)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTD] using hh
  have hk := cubic_generated_component_kernel_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  have hlocalC : ∀ i j, i ≠ j → M i ⊓ centralizer (S i : Set G) ≤ M j := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact (h.centralizer_LT_at structural).le.trans (hQTA.trans hTD)
    · intro x hx
      have hxC : (⟨x,hx.1⟩ : D) ∈ centralizer (W.subgroupOf D : Set D) := by
        intro w hw
        apply Subtype.ext
        exact mem_centralizer_iff.mp hx.2 w hw
      have hxQ : (⟨x,hx.1⟩ : D) ∈ pCore 2 D := hk ▸ hxC
      exact (le_sup_right : (T : Subgroup G) ≤ A) (hQTD (mem_map_of_mem D.subtype hxQ))
    · exact (hij rfl).elim
  have hmap (i : Bool) (g : E) :
      ((S₀ i).conjBy g).map E.subtype = (S i).conjBy (g : G) := by
    rw [map_conjBy_hom,map_subgroupOf_eq_of_le (hSE i)]
    rfl
  have hgen := ChapterF.Section07.Geometry.family_generates A D
  have hle₀ : ∀ i, S₀ i ≤ M₀ i := by
    intro i x hx
    have hh : (x : G) ∈ M i := hSM i hx
    cases i <;> exact hh
  have hn₀ : ∀ i, M₀ i ≤ normalizer (S₀ i : Set E) := by
    intro i
    have hh := (comap_mono (f := E.subtype) (hnM i)).trans (le_normalizer_comap E.subtype)
    cases i <;> exact hh
  have hC₀ : ∀ i j, i ≠ j → M₀ i ⊓ centralizer (S₀ i : Set E) ≤ M₀ j := by
    intro i j hij x hx
    have hxM : (x : G) ∈ M i := by cases i <;> exact hx.1
    have hxC : (x : G) ∈ centralizer (S i : Set G) := by
      apply mem_centralizer_iff.mpr
      intro y hy
      exact congrArg Subtype.val (mem_centralizer_iff.mp hx.2 (⟨y,hSE i hy⟩ : E) hy)
    have hh := hlocalC i j hij ⟨hxM,hxC⟩
    cases j <;> exact hh
  have hc := cubic_generated_component_seed_family_commutes_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  have hc₀ : ∀ i j (g k : E), (S₀ i).conjBy g ⊓ (S₀ j).conjBy k ≠ ⊥ →
      ⁅(S₀ i).conjBy g,(S₀ j).conjBy k⁆ = ⊥ := by
    intro i j g k hi
    have hi' : (S i).conjBy (g : G) ⊓ (S j).conjBy (k : G) ≠ ⊥ := by
      rw [←hmap i g,←hmap j k,←map_inf _ _ _ E.subtype_injective]
      exact fun hz => hi ((map_eq_bot_iff_of_injective _ E.subtype_injective).mp hz)
    apply (map_eq_bot_iff_of_injective _ E.subtype_injective).mp
    rw [map_commutator,hmap,hmap]
    exact hc i j g k hi'
  obtain ⟨hfix,hcomm⟩ := CosetGeometry.RankTwo.conjugate_seeds_in_overlap M₀ S₀ hgen hle₀ hn₀ hC₀ hc₀
  let N := conjugateSpanBy V E
  have hNA : N ≤ A := by
    apply (closure_le _).mpr
    rintro x ⟨g,hg,v,hv,rfl⟩
    have hh := hfix false (⟨g,hg⟩ : E)
    have hm := map_mono (f := E.subtype) (hh.trans inf_le_left)
    rw [hmap] at hm
    have hMA : (M₀ false).map E.subtype = A := map_subgroupOf_eq_of_le le_sup_left
    rw [hMA] at hm
    exact hm (mem_map_of_mem _ hv)
  have hNC : N ≤ centralizer (V : Set G) := by
    apply (closure_le _).mpr
    rintro x ⟨g,hg,v,hv,rfl⟩
    have hh := congrArg (map E.subtype) (hcomm false false 1 (⟨g,hg⟩ : E))
    rw [map_commutator,hmap,hmap,Subgroup.map_bot] at hh
    change ⁅V.conjBy 1,V.conjBy g⁆ = ⊥ at hh
    rw [conjBy_one] at hh
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh))
      (mem_map_of_mem _ hv)
  have hNQ : N ≤ A.pCoreIn 2 := (le_inf hNA hNC).trans (h.centralizer_LT_at structural).le
  have hNp : IsPGroup 2 N := (isPGroup_pCoreIn 2 A).to_le hNQ
  have hNne : N ≠ ⊥ := fun hz => h.chosen.ne_bot (eq_bot_iff.mpr
    ((le_conjugateSpanBy V E).trans hz.le))
  have hu : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  have hcontrol : normalizer (N : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal
      (fun M hM hAM => Set.mem_singleton_iff.mp ((h.maximal_unique_at structural).2 ▸
        show M ∈ {M : Subgroup G | IsMaximalTwoLocal M ∧ A ≤ M} from ⟨hM,hAM⟩))
      hNp hNne (le_sup_left.trans (le_normalizer_conjugateSpanBy V E))
  exact hout (((le_sup_left.trans le_sup_right : Y ≤ D).trans le_sup_right).trans
    ((le_normalizer_conjugateSpanBy V E).trans hcontrol))

/-- The original full point-normality interface. -/
theorem cubic_generated_no_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) : False := by
  apply cubic_generated_no_component_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- Source 14.5.8 in the normal-point branch used by the small-chief exclusion. -/
theorem cubic_generated_solvable_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    Group.IsSolvable (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G) := by
  classical
  by_contra hs
  obtain ⟨J,hJD,hJ,_⟩ := cubic_generated_nonsolvable_component_of_normalizes_point
    h hab structural previous faithful Y hYH hYL hYp hYT hout he hs
  exact cubic_generated_no_component_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he (J.subgroupOf _) hJ

/-- The original full point-normality interface. -/
theorem cubic_generated_solvable
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    Group.IsSolvable (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G) := by
  apply cubic_generated_solvable_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04 in
/-- The original order-four interval yields a solvable cubic completion, retaining
the selected Y, its exact original star kernel and its S₃ overgroup quotient. -/
theorem extraspecial_four_interval_cubic_solvable
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 ∧
      Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      Group.IsSolvable (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G) := by
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he⟩ :=
    extraspecial_four_interval_escaping_symmetricThree h hab structural previous hex hcard hexp
      N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  exact ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,
    cubic_generated_solvable h hab structural previous faithful hn Y hYH hYp hYT hout he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.GuardedSource

end
