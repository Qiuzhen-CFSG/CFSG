module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoRegular
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneQuadrangularConsumers

/-!
# The strict distance-two branch in the original Chapter 12 consumer

The original prepared parabolics are nonsolvable. The source construction
therefore excludes D = Z at every opposite neighbor of a noncommuting
critical path, in either vertex orbit, and preserves strictness under the
actual reduced-completion inclusion. Together with the completed b=1
comparisons this narrows the original noncommuting consumer to the precise
D > Z hypotheses of DGS (10.10).

The base-edge application also supplies the saturated alpha core, the
beta-core product and its Frattini and derived subgroups, and the elementary
alpha-core quotient of order q_beta squared. These are the full original
parabolic cores, including both odd Borel factors. Every earlier action,
centrality, commutator and model-selection premise is discharged from the
same F.1.11 input.

The actual GlobalExit application retains the strict b=2 branch: residual
separation, path parameters and marked recognition remain necessary there.
The other original source branches and general Chapter 15 restoration are
unchanged obligations of the source assembly.

Source: DGS (1985), (10.6)--(10.10), pp.157--165; Aschbacher--Smith
F.1.11--F.1.12 and 12.2.2, pp.263--264,795--796.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.Assembly
universe u
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
local notation "F" => Reduction.reducedFamily ![L,R] (sourceS L H)
local notation "ι" => Subgroup.subtype (G₀ ![L,R] (sourceS L H))

/-- Every original nonsolvable noncommuting pair either has its full comparison
or is in the strict distance-two D > Z branch, in its actual vertex orientation. -/
theorem comparison_or_strict_bTwo_of_noncommuting_source
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {v w : Vertex F} (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) :
    (ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) ∧
      ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ sourceS L H ≤ R) ∨
    (b F = 2 ∧ ∃ m : Vertex F, (graph F).Adj v m ∧ (graph F).Adj m w ∧
      Z F m ≤ centerIn (graphLocalGroup F m) ∧
      ∀ t : Vertex F, (graph F).Adj v t → t ≠ m →
        Z F v < NoncommutingProfile.D F m t ∧
        (Z F v).map ι < (Q F m).map ι ⊓ (Q F t).map ι) := by
  rcases d.comparison_or_bTwo_of_noncommuting_source h hTH hp hc hne with hh | hb
  · exact Or.inl hh
  · exact Or.inr ⟨hb,BTwoSource.strict_core_intersections_of_critical_bTwo
      (d.hypothesisF11 h hTH) (d.parabolics_not_solvable h hp) hc hne hb⟩

/-- The literal original cores in the distance-two branch have the Chapter 10
Frattini, derived, and elementary-section structure, with a nonbinary beta parameter. -/
theorem core_layers_of_critical_bTwo_source
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    {u t : Vertex F}
    (hc : IsCriticalPair F (base F false) u)
    (hne : ⁅Z F (base F false),Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj (base F true) u)
    (ht : (graph F).Adj (base F false) t) (htne : t ≠ base F true) :
    let Q₀ := (parabolic ![L,R] (sourceS L H) 0).pCoreIn 2
    let Q₁ := (parabolic ![L,R] (sourceS L H) 1).pCoreIn 2
    let D₀ := Q₁ ⊓ (Q F t).map ι
    let Z₁ := (Z F (base F true)).map ι
    ∃ m : ℕ, 1 < m ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^m) ∧
      D₀ ≠ (Z F (base F false)).map ι ∧
      (centralSeed F (base F false) (base F true) t).map ι = Q₀ ∧
      Q₁ = (V F (base F true) 1).map ι ⊔ D₀ ∧
      (frattini Q₁).map Q₁.subtype = Z₁ ∧ ⁅Q₁,Q₁⁆ = Z₁ ∧
      P₀ ![L,R] (sourceS L H) 0 ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      B₀ ![L,R] (sourceS L H) ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      ∃ hN : (D₀.subgroupOf Q₀).Normal, letI := hN
        IsElementaryAbelian 2 (Q₀ ⧸ D₀.subgroupOf Q₀) ∧
        Nat.card (Q₀ ⧸ D₀.subgroupOf Q₀) = (2^m)^2 := by
  obtain ⟨k,f,fin,ch,a,c,hactor,hk,m,hm,hR,hpow,hext,hD,hs,hQ,hPhi,hder,hbound,
    hnP,hnB,hN,hE,hcard⟩ := BTwoSource.original_core_layers
      (d.hypothesisF11 h hTH) hc hne hb hβu ht htne (d.parabolics_not_solvable h hp 0)
  exact ⟨m,hm,hR,hD,hs,hQ,hPhi,hder,hnP,hnB,hN,hE,hcard⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.OriginalExtension
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
include D h hmany hn hpsl hH

/-- Chapter 12 retains the original comparison or a strict regular-branch
core intersection; the exceptional equality is excluded in either orientation. -/
theorem rankOne_comparison_or_strict_bTwo_of_noncommuting_source
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    {v w : Vertex (Reduction.reducedFamily ![L,R] (Global.sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) w⁆ ≠ ⊥) :
    (Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∧
      ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R) ∨
    (let F := Reduction.reducedFamily ![L,R] (Global.sourceS L H)
     let ι := (G₀ ![L,R] (Global.sourceS L H)).subtype
     b F = 2 ∧ ∃ m : Vertex F, (graph F).Adj v m ∧ (graph F).Adj m w ∧
      Z F m ≤ centerIn (graphLocalGroup F m) ∧
      ∀ t : Vertex F, (graph F).Adj v t → t ≠ m →
        Z F v < NoncommutingProfile.D F m t ∧
        (Z F v).map ι < (Q F m).map ι ⊓ (Q F t).map ι) :=
  d.comparison_or_strict_bTwo_of_noncommuting_source
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hc hne

/-- The full residual consumer retains only the strict distance-two source
branch after consuming both actual b=1 marked comparisons. -/
theorem rankOne_globalExit_or_strict_bTwo_of_noncommuting_source
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    {v w : Vertex (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) v w)
    (hne : ⁅Z (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) v,
      Z (Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)) w⁆ ≠ ⊥) :
    RankOneModule.GlobalExit G ∨
    (let F := Reduction.reducedFamily ![L,residual H] (Global.sourceS L H)
     let ι := (G₀ ![L,residual H] (Global.sourceS L H)).subtype
     b F = 2 ∧ ∃ m : Vertex F, (graph F).Adj v m ∧ (graph F).Adj m w ∧
      Z F m ≤ centerIn (graphLocalGroup F m) ∧
      ∀ t : Vertex F, (graph F).Adj v t → t ≠ m →
        Z F v < NoncommutingProfile.D F m t ∧
        (Z F v).map ι < (Q F m).map ι ⊓ (Q F t).map ι) := by
  rcases D.rankOne_comparison_or_strict_bTwo_of_noncommuting_source
    h hmany hn hpsl hH d hp hc hne with hh | hb
  · exact Or.inl (D.rankOne_globalExit_of_prepared_comparison h hmany hn hpsl hH d hp hh.1)
  · exact Or.inr hb

/-- Literal Chapter 12 core-layer application with the original L, selected R,
full parabolic cores, Borel, and original inclusion. -/
theorem rankOne_core_layers_of_critical_bTwo_source
    {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    {u t : Vertex (Reduction.reducedFamily ![L,R] (Global.sourceS L H))}
    (hc : IsCriticalPair (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false) u)
    (hne : ⁅Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H))
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false),
      Z (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) u⁆ ≠ ⊥)
    (hb : b (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) = 2)
    (hβu : (graph (Reduction.reducedFamily ![L,R] (Global.sourceS L H))).Adj
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true) u)
    (ht : (graph (Reduction.reducedFamily ![L,R] (Global.sourceS L H))).Adj
      (base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) false) t)
    (htne : t ≠ base (Reduction.reducedFamily ![L,R] (Global.sourceS L H)) true) :
    let F := Reduction.reducedFamily ![L,R] (Global.sourceS L H)
    let ι := (G₀ ![L,R] (Global.sourceS L H)).subtype
    let Q₀ := (parabolic ![L,R] (Global.sourceS L H) 0).pCoreIn 2
    let Q₁ := (parabolic ![L,R] (Global.sourceS L H) 1).pCoreIn 2
    let D₀ := Q₁ ⊓ (Q F t).map ι
    let Z₁ := (Z F (base F true)).map ι
    ∃ m : ℕ, 1 < m ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2^m) ∧
      D₀ ≠ (Z F (base F false)).map ι ∧
      (centralSeed F (base F false) (base F true) t).map ι = Q₀ ∧
      Q₁ = (DGS85.V F (base F true) 1).map ι ⊔ D₀ ∧
      (frattini Q₁).map Q₁.subtype = Z₁ ∧ ⁅Q₁,Q₁⁆ = Z₁ ∧
      P₀ ![L,R] (Global.sourceS L H) 0 ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      B₀ ![L,R] (Global.sourceS L H) ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      ∃ hN : (D₀.subgroupOf Q₀).Normal, letI := hN
        IsElementaryAbelian 2 (Q₀ ⧸ D₀.subgroupOf Q₀) ∧
        Nat.card (Q₀ ⧸ D₀.subgroupOf Q₀) = (2^m)^2 :=
  d.core_layers_of_critical_bTwo_source
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp hc hne hb hβu ht htne

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
