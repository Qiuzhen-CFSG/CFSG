module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.SourceAssembly
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.ThompsonWitness
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.Alternatives
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.PointModule
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.SectionCentralizers

/-!
# The Goldschmidt rank-three conclusion from the earlier source implications

The literal source geometry gives the two vertices inside I. Five noncentral
binary chief factors contradict the universal F.6.5 bound if O₂(I) is trivial.
The resulting elementary V_I and its exact core centralizer give the faithful
plus action. Source normalizer escape and 14.3.9(2), with uniqueness over LT,
force the Thompson subgroup outside this kernel. Adequate B.5.6 then supplies
the actual small subnormal subgroup. The full F.6 comparison recognizes the
bang quotient and removes its kernel over the plus quotient, marking both
original parabolics. H.5.5 finally identifies the original V_I as natural and
proves its prime rank is three.

Every local classification conclusion is constructed here. The universal
earlier implications remain explicit: Structural1222 belongs to qt-12-02,
Uniqueness127 to qt-1-02-adequate-assembly, the Thompson and faithful-family
implications to qt-14-03-prelim, adequate B.5.6 to qt-b05-general-classification,
the amalgam bound to qt-f06-amalgams, and full F.6.18 and F.6.13 to qt-f-06
and its source owners. The A.1.31 section-centralizer input is discharged by
`ChapterF.Noncyclic.sectionCentralizerInput`. Geometry, the
compatible upper marking and the source commutator identity are supplied by
the earlier 14.7 preparation owner on the same original datum. No local triple,
core, Thompson, parabolic-marking or rank-three conclusion is an input.

The precise 14.3.9(2) contract is `ThompsonWitness.EarlierThompsonNormality`
in `QuotientComparison/ThompsonWitness/Action.lean`: for every source
counterexample and higher-rank natural flag, containment of J(T) in R₁
implies its relative normality in LT. The 14.3.4(1–2) contract is
`EarlierFaithfulClassification` in Section04's
`LocalAction/FullAction/Components/Selection.lean`: every faithful local
component has two-core quotient A₅ or L₃(2), is normal in its join with T,
and belongs to the maximal local family. Both remain with qt-14-03-prelim.

Source: Aschbacher–Smith, proof of 14.7.70, printed pp.1074–1075
(PDF pp.1091–1092), manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Stellmacher
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.SourceCompletion
open Chapter12.Section08 QuotientComparison
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)

/-- The source Thompson step needs only the structural and uniqueness
implications from the larger setup record. -/
private theorem thompson_escape (geometry : Geometry d c) (core : CoreFacts c)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (thompson : ThompsonWitness.EarlierThompsonNormality.{u}) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (I c).pCoreIn 2 := by
  intro hJ
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hn := thompson G T L V d.counterexample d.natural F
    (hJ.trans (ThompsonWitness.core_le_R₁ c))
  have hLT : L ⊔ (T : Subgroup G) ≤
      normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hJT.trans le_sup_right)).mp hn
  have hu := (d.natural.maximal_unique structural uniqueness).2
  have hNM := normalizer_le_of_unique_maximalTwoLocal
    (J := L ⊔ (T : Subgroup G))
    (fun N hN hLN => Set.mem_singleton_iff.mp (hu ▸
      show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
        from ⟨hN,hLN⟩))
    (T.isPGroup'.to_le hJT) (ThompsonWitness.thompson_ne_bot d) hLT
  exact ThompsonWitness.normalizer_escape d c geometry core structural
    ((Y_le_I c).trans ((I_normalizes_thompson_of_le_core c hJ).trans hNM))

variable
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (thompson : ThompsonWitness.EarlierThompsonNormality.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (b5 : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (amalgams : ∀ (H : Type u) [Group H] [Finite H] (A B : Subgroup H),
      ChapterF.IsGoldschmidtTriple A B → pCore 2 H = ⊥ → Nat.card A ≤ 384)

include structural uniqueness thompson faithful b5 amalgams

/-- The actual core and small subnormal witness, before applying the full
F.6 quotient classification. Every local B.5 premise is discharged. -/
theorem core_and_small (geometry : Geometry d c)
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    CoreFacts c ∧
      pCore 2 (I c) = centralizer ((VI c).subgroupOf (I c) : Set (I c)) ∧
      SmallSubnormal c := by
  obtain ⟨core,hcore⟩ := TripleCore.SourceAssembly.coreFacts_of_source
    d c geometry structural uniqueness mark hcomm amalgams
  have hJ := thompson_escape d c geometry core structural uniqueness thompson
  have alternative := ThompsonWitness.nontrivial_adequate_alternative d c geometry core b5 hJ
  exact ⟨core,hcore,ThompsonWitness.ComponentSelection.smallSubnormal_of_adequate
    d c geometry core faithful alternative⟩

variable
    (sourceF : FSource.ClassificationInput KnownSimple.IsKnownSimple.{u})
    (rigidity : ChapterF.Noncyclic.GoldschmidtRigidityInput.{u})
include sourceF rigidity

/-- The actual core and both marked quotient parabolics, with the source
triple, five-factor obstruction, B.5 witness and every F.6 comparison supplied. -/
theorem core_and_marking (geometry : Geometry d c)
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    CoreFacts c ∧
      pCore 2 (I c) = centralizer ((VI c).subgroupOf (I c) : Set (I c)) ∧
      pPrimeCore 3 (I c) = pCore 2 (I c) ∧ Nonempty (ParabolicMarking c) := by
  obtain ⟨core,hcore,small⟩ := core_and_small d c structural uniqueness thompson
    faithful b5 amalgams geometry mark hcomm
  obtain ⟨recognition⟩ := Alternatives.bangRecognition_of_inputs
    d c sourceF rigidity ChapterF.Noncyclic.sectionCentralizerInput geometry core small
  obtain ⟨hprime,marked⟩ := core_and_marking_of_bangRecognition c core recognition
  exact ⟨core,hcore,hprime,marked⟩

/-- H.5.5 on the original point-generated subgroup, after constructing all
of the local Goldschmidt classification outputs from the earlier source inputs. -/
theorem primeRank_VI (geometry : Geometry d c)
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) : primeRank 2 (VI c) = 3 := by
  obtain ⟨core,_,_,⟨parabolics⟩⟩ := core_and_marking d c structural uniqueness thompson
    faithful b5 amalgams sourceF rigidity geometry mark hcomm
  exact PointModule.primeRank_VI d c core parabolics geometry

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.SourceCompletion
