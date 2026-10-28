module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.G2Source
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.G2Chapter12

/-!
# The linear hexagon source row in the original Chapter 12 pair

Apply the source G₂ construction to the literal reduced Sylow and restore
the whole common Borel. Converting the constructed short-root index to the
native orientation changes none of the three group maps. The existing
Chapter 15 restoration then constructs the original comparison and the
original right-core equality and Sylow containment for every prepared
perfect selected factor.

Only the earlier marked split quotient, hexagon parameter, original linear
quotient marks over a common field and root reflections are supplied.
There is no assumed reduced G₂ comparison, kernel bound, local-action
identification or generation premise. The source construction includes
G₂(2); the original consumer excludes it using its own nonsolvability.
Exhaustive row selection and construction of the remaining earlier inputs
stay with DGS source assembly.

Source: DGS, Groups and Graphs (1985), Theorem D and (15.2), pp.224,226--228;
Aschbacher--Smith F.1.12 and the chosen-module argument, printed p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Atlas.G2.RootPresentationRecognition
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.G2Source
open FongSeitzBinary OriginalExtension SuzukiContainment

private def nativeOrientation (i : Fin 2) : Bool := decide (i = 0)

private def flagNativeIso (F : Type*) [Field F] (i : Fin 2) :
    Iso (flagAmalgam F i) (G2Native.amalgam F (nativeOrientation i)) := by
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun z => Fin.elim0 z) k) i
  · exact Iso.refl _
  · exact Iso.refl _

private theorem flagNativeIso_left (F : Type*) [Field F] (i : Fin 2)
    (x : flagVertex F i 0) : ((flagNativeIso F i).left x : Atlas.G2.Model F) = x := by
  fin_cases i <;> rfl

private theorem flagNativeIso_right (F : Type*) [Field F] (i : Fin 2)
    (x : flagVertex F i 1) : ((flagNativeIso F i).right x : Atlas.G2.Model F) = x := by
  fin_cases i <;> rfl

private theorem flagNativeIso_middle (F : Type*) [Field F] (i : Fin 2)
    (x : Atlas.G2.borel (K := F)) :
    ((flagNativeIso F i).middle x : Atlas.G2.Model F) = x := by
  fin_cases i <;> rfl

variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (h : HypothesisF11 L S) (Q : MarkedQuotient P)
  (e : Iso
    (ofSubgroups (parabolic L (reducedSylow L S) 0)
      (parabolic L (reducedSylow L S) 0 ⊓ parabolic L (reducedSylow L S) 1)
      (parabolic L (reducedSylow L S) 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) (hm : rotationOrder Q = 6)
  (μ : ∀ i, (L i ⧸ pCore 2 (L i)) ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i)

/-- The constructed reduced comparison in its native orientation, retaining
each original endpoint representative and the whole reduced Borel. -/
theorem reduced_linear_recognition :
    ∃ short : Bool, ∃ c : Iso (reducedAmalgam L S) (G2Native.amalgam F short),
      (∀ x : parabolic L (reducedSylow L S) 0,
        (c.left x : Atlas.G2.Model F) =
          linearModelEquiv Q e (reduced_hypothesis h) split hm μ n
            (MarkedLocal.endpointMap Q e 0 x)) ∧
      (∀ x : parabolic L (reducedSylow L S) 1,
        (c.right x : Atlas.G2.Model F) =
          linearModelEquiv Q e (reduced_hypothesis h) split hm μ n
            (MarkedLocal.endpointMap Q e 1 x)) ∧
      (∀ b : commonBorel L (reducedSylow L S),
        (c.middle b : Atlas.G2.Model F) =
          linearModelEquiv Q e (reduced_hypothesis h) split hm μ n
            (MarkedLocal.borelMap Q e (reduced_hypothesis h) b)) := by
  let hr := reduced_hypothesis h
  let k := (linearData Q e hr split hm μ n).1
  let j : Iso (reducedAmalgam L S)
      (ofSubgroups (parabolic L (reducedSylow L S) 0)
        (parabolic L (reducedSylow L S) 0 ⊓ parabolic L (reducedSylow L S) 1)
        (parabolic L (reducedSylow L S) 1) inf_le_left inf_le_right) :=
    NativeRestoration.subgroupCongrIso _ _ _ _ rfl (lemma_F_1_3_6 hr).symm rfl
  let c := (j.trans (linearComparison Q e hr split hm μ n)).trans (flagNativeIso F k)
  refine ⟨nativeOrientation k, c, ?_, ?_, ?_⟩
  · intro x
    change ((flagNativeIso F k).left _ : Atlas.G2.Model F) = _
    rw [flagNativeIso_left]
    exact linearComparison_left Q e hr split hm μ n x
  · intro x
    change ((flagNativeIso F k).right _ : Atlas.G2.Model F) = _
    rw [flagNativeIso_right]
    exact linearComparison_right Q e hr split hm μ n x
  · intro b
    change ((flagNativeIso F k).middle _ : Atlas.G2.Model F) = _
    rw [flagNativeIso_middle]
    exact linearComparison_borel Q e hr split hm μ n b

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.G2Source

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.DGS85 ChapterF.Source.FongSeitzBinary
open OriginalExtension SuzukiContainment
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  {P : Fin 2 → Subgroup X}

/-- On the original selected pair the linear hexagon source inputs construct
the full comparison, right two-core equality and the same Sylow containment.
Perfectness of R is the unchanged consumer hypothesis. -/
theorem comparison_and_core_of_reduced_linear_hexagon
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (Q : MarkedQuotient P)
    (e : Iso
      (sourceParabolicAmalgam ![L,R] (reducedSylow ![L,R] (sourceS L H)))
      Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 6)
    (μ : ∀ i, (![L,R] i ⧸ pCore 2 (![L,R] i)) ≃* PSL(2,F))
    (s : ∀ i, RootReflection Q split i) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) ∧
      (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ sourceS L H ≤ R := by
  obtain ⟨short,c,_⟩ := Assembly.G2Source.reduced_linear_recognition
    (d.hypothesisF11 h hTH) Q e split hm μ s
  exact ⟨DGS85.OriginalExtension.concreteComparison_of_reduced_g2 d h hTH hp F short c,
    DGS85.OriginalExtension.g2_original_core_and_containment_of_reduced_iso
      d h hTH hp F short c⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.SuzukiContainment
variable {G X : Type*} [Group G] [Finite G] [Group X]
  {T : Sylow 2 G} {L V H A B R : Subgroup G} {P : Fin 2 → Subgroup X}

/-- The literal chosen-module consumer now requires earlier source geometry
and linear quotient marks instead of a reduced G₂ recognition premise. -/
theorem rankOne_global_comparison_and_core_of_linear_hexagon
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (Q : MarkedQuotient P)
    (e : Iso
      (Global.sourceParabolicAmalgam ![L,R]
        (reducedSylow ![L,R] (Global.sourceS L H))) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 6)
    (μ : ∀ i, (![L,R] i ⧸ pCore 2 (![L,R] i)) ≃* PSL(2,F))
    (s : ∀ i, RootReflection Q split i) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∧
      (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R :=
  d.comparison_and_core_of_reduced_linear_hexagon
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp F Q e split hm μ s

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
