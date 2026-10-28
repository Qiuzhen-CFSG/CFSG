module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementarySourceRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryMarkedConsumers

/-!
# Original-pair elementary commuting-edge consumers without quotient premises

The prepared right factor is nonsolvable, so its actual enlarged local
quotient cannot be PSL2(2). The source construction therefore supplies the
nonbinary elementary marked U4 comparison. Chapter 15 restoration gives the
ORIGINAL pair comparison, with the full Borel and both endpoint squares.
The Chapter 12 application retains full KnownSimple and the same arbitrary
selected perfect factor. No finite split quotient or rotation is supplied.

This closes the elementary branch for these nonsolvable consumers. The
unrestricted binary branch and nonelementary source assembly remain open.
Source: DGS, Groups and Graphs (1985), (11.7), pp.174--175,
Theorem D and (15.2), pp.224,226--228; Aschbacher--Smith F.1.12 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Reduction OriginalExtension SuzukiContainment Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem original_beta_quotient_nonbinary_of_nonsolvable
    (h : HypothesisF11 L S) (hns : ¬ Group.IsSolvable (parabolic L S 1)) :
    ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
        (G₀ L S).subtype ⧸ pCore 2
          ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
            (G₀ L S).subtype)) 2 2 := by
  intro he
  let M := (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
    (G₀ L S).subtype
  have hquot : Group.IsSolvable (M ⧸ pCore 2 M) := by
    obtain ⟨k,fk,fink,hk,⟨e⟩⟩ := he
    let _ := fk
    let _ := fink
    let : Group.IsSolvable PSL(2,k) := Theory.PSL2.OuterSolvable.isSolvable_of_card_two hk
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let _ := hquot
  let : Group.IsNilpotent (pCore 2 M) := (pCore_isPGroup (p := 2) (G := M)).isNilpotent
  let : Group.IsSolvable M := (Group.isSolvable_iff_subgroup_quotient (pCore 2 M)).mpr
    ⟨inferInstance,inferInstance⟩
  have hLM : L 1 ≤ M := by
    change L 1 ≤ (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
      (G₀ L S).subtype
    rw [reduced_graphLocalGroup_image h]
    exact (local_le_starredParabolic 1).trans le_sup_left
  let : Group.IsSolvable (L 1) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hLM)
  exact hns ((h.parabolic_solvable_iff_local_quotient 1).mpr inferInstance)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.CommutingOneProfile
open ChapterF.Source.DGS85.OriginalExtension ChapterF.Source.SuzukiContainment
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}

/-- Restore the original pair from its literal elementary commuting-edge
branch. The prepared nonsolvable parabolics discharge the local catalogues;
the source constructs its entire marked reduced comparison. -/
theorem comparison_of_commuting_one_elementary_source
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (sourceS L H)) false)
      (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true))
    (hb : b (Reduction.reducedFamily ![L,R] (sourceS L H)) = 1)
    (hcomm : ⁅Z (Reduction.reducedFamily ![L,R] (sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (sourceS L H)) false),
      Z (Reduction.reducedFamily ![L,R] (sourceS L H))
        (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true)⁆ = ⊥)
    (helem : letI := QuadrangleStructure.original_core_normal_in_sylow (L := ![L,R]) (S := reducedSylow ![L,R] (sourceS L H)) 1
      IsElementaryAbelian 2 (reducedSylow ![L,R] (sourceS L H) ⧸
        ((parabolic ![L,R] (reducedSylow ![L,R] (sourceS L H)) 1).pCoreIn 2).subgroupOf
          (reducedSylow ![L,R] (sourceS L H)))) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  let hf := d.hypothesisF11 h hTH
  let := QuadrangleStructure.original_core_normal_in_sylow
    (L := ![L,R]) (S := reducedSylow ![L,R] (sourceS L H)) 1
  have hfull : ∃ hn : (((Q (Reduction.reducedFamily ![L,R] (sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true)).map
        (Reduction.G₀ ![L,R] (sourceS L H)).subtype).subgroupOf
          (twoCore (commonBorel ![L,R] (sourceS L H)))).Normal,
      letI := hn
      IsElementaryAbelian 2 (twoCore (commonBorel ![L,R] (sourceS L H)) ⧸
        ((Q (Reduction.reducedFamily ![L,R] (sourceS L H))
          (base (Reduction.reducedFamily ![L,R] (sourceS L H)) true)).map
            (Reduction.G₀ ![L,R] (sourceS L H)).subtype).subgroupOf
              (twoCore (commonBorel ![L,R] (sourceS L H)))) := by
    have hq := (ChapterF.Source.DGS85.NoncommutingProfile.reduced_base_Q_map hf true).trans
      (reduced_parabolic_core hf 1).symm
    rw [hq]
    change ∃ hn : (((parabolic ![L,R] (reducedSylow ![L,R] (sourceS L H)) 1).pCoreIn 2).subgroupOf
      (reducedSylow ![L,R] (sourceS L H))).Normal,
      letI := hn
      IsElementaryAbelian 2 (reducedSylow ![L,R] (sourceS L H) ⧸
        ((parabolic ![L,R] (reducedSylow ![L,R] (sourceS L H)) 1).pCoreIn 2).subgroupOf
          (reducedSylow ![L,R] (sourceS L H)))
    exact ⟨QuadrangleStructure.original_core_normal_in_sylow
      (L := ![L,R]) (S := reducedSylow ![L,R] (sourceS L H)) 1,helem⟩
  obtain ⟨m,hm,⟨f⟩⟩ := original_elementary_nonbinary_reduced_comparison
    hf hc hb hcomm hfull
    (original_beta_quotient_nonbinary_of_nonsolvable hf (d.parabolics_not_solvable h hp 1))
  exact d.concreteComparison_of_reduced_alternatives h hTH hp (.unitaryFour m hm false ⟨f⟩)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.CommutingOneProfile
open ChapterF.Source.DGS85.OriginalExtension ChapterF.Source.SuzukiContainment
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
  (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
    (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false)
    (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true))
  (hb : b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 1)
  (hcomm : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false),
    Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true)⁆ = ⊥)
  (helem : letI := QuadrangleStructure.original_core_normal_in_sylow (L := ![L,R]) (S := reducedSylow ![L,R] (Global.sourceS L H)) 1
    IsElementaryAbelian 2 (reducedSylow ![L,R] (Global.sourceS L H) ⧸
      ((parabolic ![L,R] (reducedSylow ![L,R] (Global.sourceS L H)) 1).pCoreIn 2).subgroupOf
        (reducedSylow ![L,R] (Global.sourceS L H))))

include D h hmany hn hpsl hH d hp hc hb hcomm helem in
/-- The full KnownSimple chosen-module consumer on the same selected perfect
factor. No profile, finite quotient, split data or root-sign premise remains. -/
theorem rankOne_comparison_of_commuting_one_elementary_source :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) :=
  d.comparison_of_commuting_one_elementary_source
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp
    hc hb hcomm helem

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
