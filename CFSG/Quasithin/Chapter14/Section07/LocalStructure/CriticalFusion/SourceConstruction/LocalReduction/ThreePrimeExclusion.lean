module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreePrimeActor
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreePrimeRecognition
public import BenderSuzuki.External.Huppert.XI.theorem_3_6

/-!
# Source 14.7.7 for the original local family

Normality of the actual point cubic in I/O₂(I) forces its full
three-prime core to vanish. A nonzero core supplies a genuine Suzuki
component and the literal reduced local with its quadratic actor. Apply
the normal-or-exchanged full-movement contradiction on that same quotient.
No solvability or natural-recognition premise is added.

Source: Aschbacher–Smith, 14.7.7, printed p.1045, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Source 14.7.7 on the original local family: normality of the actual point
cubic eliminates the full three-prime core, without a solvability hypothesis. -/
theorem local_threePrimeCore_eq_bot_of_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hn : (((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))).Normal) :
    pPrimeCore 3 (HStar I) = ⊥ := by
  by_contra hne
  obtain ⟨K,m,hK,hm,hK3,hker,⟨eK⟩,hJI,hJ,hKJ,⟨eJ⟩,hkJ,horbit,hnX,hcX,hgen,
    hnJ,hnZ,hcZ,hcomm,hmoved,hU,a,hfree,hq,A,hAR,hA,hquad,hcod,hfaith⟩ :=
    local_threePrime_reduced_actor h hab structural previous faithful I hI hn hne
  let N := conjugateSpanBy (K.map I.subtype) (T : Subgroup G)
  let J := N ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  let KJ := (K.map I.subtype).subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let B := KJ.map q
  let X := (N.subgroupOf J).map q
  let Z := ((F.Li L 1).subgroupOf J).map q
  let := hU
  let S : Sylow 2 (HStar J) :=
    (T.subtype (F.sylow_le_of_mem_Hz hJ)).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  let : Group.IsNilpotent (pCore 2 J) := pCore_isPGroup.isNilpotent
  have hB : B.IsCComponent := hKJ.map_quotient (pCore 2 J)
  let eB := (cComponentTwoCoreQuotientEquiv hKJ).symm.trans eJ
  let : Group.IsPerfect B := hB.perfect
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
  let : IsSimpleGroup B := eB.isSimpleGroup
  have hz := Chapter13.Section08.Components.Suzuki.NaturalSections.SectionRecognition.center_eq_bot_of_equiv_suzuki eB
  let : IsQuasisimple B := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hidx := Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
    (ChapterE.Structure.sqtk_two_quotient (local_star_sqtk h J hJ) (pCore 2 (HStar J)) pCore_isPGroup) hB
  have hi : B.Normal ∨ (normalizer (B : Set (HStar J))).index = 2 := hidx.imp_right And.left
  have hXS : X = componentOrbit B (S : Subgroup (HStar J)) := by
    change X = conjugateSpanBy B (S : Subgroup (HStar J)) at horbit
    exact horbit.trans (conjugateSpanBy_eq_iSup_conj _ _)
  have hRT : F.Ri L 1 ≤ (T : Subgroup G) := by
    let E := F.Li L 1 ⊔ (T : Subgroup G)
    have hh := pCoreIn_le_sylow E (T.subtype (show (T : Subgroup G) ≤ E from le_sup_right))
    change E.pCoreIn 2 ≤ (T : Subgroup G)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ E from le_sup_right)] using hh
  have hAS : A.map q ≤ (S : Subgroup (HStar J)) :=
    map_mono (hAR.trans (subgroupOf_mono J hRT))
  change X ≤ centralizer (Z : Set (HStar J)) at hcomm
  change A.map q ⊓ centralizer (X : Set (HStar J)) = ⊥ at hfaith
  rw [hXS] at hcomm hfaith
  exact suzuki_orbit_impossible_of_fixedFree_cubic a.representation a.faithful
    (local_star_sqtk h J hJ) B ⟨hB.subnormal,inferInstance⟩ S hi (by omega) eB
    Z (A.map q) hcZ hfree hcomm hAS hA hquad hcod hfaith

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
