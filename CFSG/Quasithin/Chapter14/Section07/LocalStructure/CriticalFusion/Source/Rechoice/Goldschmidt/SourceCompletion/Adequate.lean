module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.SourceCompletion.Noncyclic
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.DihedralPSL2

/-!
# The adequate F.6 source comparison for the original critical path

The dihedral PSL₂ alternative supplies the quasisimple generalized Fitting
subgroup, its equality with the whole group, and the original dihedral Sylow.
These are precisely the data used by the existing component comparison.
No local S₄ marking is needed. The actual bang and plus quotient maps,
subnormal witness, and point-generated module remain unchanged.

Source: Aschbacher–Smith, F.6.18 and 14.7.70, printed pp.309–310,1074–1075.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.SourceCompletion.Adequate
open Subgroup Representation Chapter12.Section08
open QuotientComparison QuotientComparison.Alternatives
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)

/-- The actual bang recognition uses only adequate ambient F.6 alternatives. -/
theorem bangRecognition
    (sourceF : FSource.AdequateClassificationInput KnownSimple.IsKnownSimple.{u})
    (h : Geometry d c) (k : CoreFacts c) (small : SmallSubnormal c) :
    Nonempty (BangRecognition c) := by
  let cover : ThreePrimeSQTKQuotient KnownSimple.IsKnownSimple
      ((I c) ⧸ pPrimeCore 3 (I c)) := {
    Cover := I c
    sqtk := (Geometry.local_and_sqtk (d := d) (c := c) k.nontrivial).2
    equiv := MulEquiv.refl _ }
  obtain ⟨S,hS,hs⟩ := sourceF _ _ _ (bang_triple d c h k small) cover
  have hne : Nat.card S ≠ 2 := fun hcard => bang_sylow_card_ne_two d c h k small
    ((Nat.card_congr ((bangSylow c).equiv S).toEquiv).trans hcard)
  have solve {A B : Subgroup ((I c) ⧸ pPrimeCore 3 (I c))}
      (ha : FSource.AdequateAlternative A B S) : Nonempty (BangRecognition c) := by
    change FSource.Alternative A B S ∨ Nonempty (FSource.DihedralPSL2Row S) at ha
    rcases ha with ha | hr
    · rcases Nonsolvable.comparison c small S hne ha with hrow | hr
      · exact (Noncyclic.not_rowTwo d c h k small hrow).elim
      · exact hr
    · obtain ⟨r⟩ := hr
      exact Nonsolvable.recognition_of_dihedral_row c small r.quasisimple r.component S r.sylow
  exact hs.elim solve solve

variable
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (thompson : ThompsonWitness.EarlierThompsonNormality.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (b5 : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (amalgams : ∀ (H : Type u) [Group H] [Finite H] (A B : Subgroup H),
      ChapterF.IsGoldschmidtTriple A B → pCore 2 H = ⊥ → Nat.card A ≤ 384)
    (sourceF : FSource.AdequateClassificationInput KnownSimple.IsKnownSimple.{u})
include structural uniqueness thompson faithful b5 amalgams sourceF

/-- The original plus quotient and both actual parabolics from adequate F.6. -/
theorem core_and_marking (geometry : Geometry d c)
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    CoreFacts c ∧
      pCore 2 (I c) = centralizer ((VI c).subgroupOf (I c) : Set (I c)) ∧
      pPrimeCore 3 (I c) = pCore 2 (I c) ∧ Nonempty (ParabolicMarking c) := by
  obtain ⟨core,hcore,small⟩ := SourceCompletion.core_and_small d c structural uniqueness
    thompson faithful b5 amalgams geometry mark hcomm
  obtain ⟨recognition⟩ := bangRecognition d c sourceF geometry core small
  obtain ⟨hprime,marked⟩ := core_and_marking_of_bangRecognition c core recognition
  exact ⟨core,hcore,hprime,marked⟩

/-- The original point-generated span has rank three with the corrected F.6 boundary. -/
theorem primeRank_VI (geometry : Geometry d c)
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) : primeRank 2 (VI c) = 3 := by
  obtain ⟨core,_,_,⟨parabolics⟩⟩ := core_and_marking d c structural uniqueness thompson
    faithful b5 amalgams sourceF geometry mark hcomm
  exact PointModule.primeRank_VI d c core parabolics geometry

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.SourceCompletion.Adequate
