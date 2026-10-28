module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ShiftedForwardClosure
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.ForwardKernel

/-!
# Shifted forward-closure exclusion for the original Baumann source

The literal characteristic replacement cannot have a normal radius subgroup
outside its Baumann subgroup whose kernel commutator is a line noncentral on
the specified nearby endpoint. The source closure proof forces an alternating
block, excluded by the actual original chief count.

Source: MS93 (5.9), second paragraph, printed pp.920--921, used for the
original Aschbacher--Smith 13.7.4(1) source through C.1.37.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
open CFSG.Quasithin.ChapterC CFSG.Quasithin.ChapterC.NaturalSixControl
open Section08.SourceCompletion Section05.PlaneGeometry
open Section08.TransvectionRecognition.Component.ModelExtension
open BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
local notation "X" => (L ⊔ (T : Subgroup G) : Subgroup G)
local notation "LX" => L.subgroupOf X

/-- The actual original source excludes the shifted controlled-line configuration. -/
theorem sourceData_shifted_controlled_line_false
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v≠1) :
    let := component_normal d
    let := local_module_normal d
    let d0 := sourceData d h hU hV v hv
    ∀ (hm : IntrinsicMSPair d0)
      (r : CharacteristicReduction ((LX).subgroupOf (LX⊔d0.B))
        (d0.B.subgroupOf (LX⊔d0.B))) {e : Vertex r.radical}
      (p : DistanceEight.PathCentrality.CriticalPath r.radical
        ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry (alpha r.radical) e),
      4<((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.b r.radical →
      ∀ f : Vertex r.radical, color r.radical f=false →
      (cosetGraph r.radical).dist e f≤2 →
      (cosetGraph r.radical).dist (p.walk.getVert (p.walk.length-2)) f≤4 →
      ∀ Y T₀ H₁ : Subgroup (FreeAmalgam r.radical),
      Y≤BinaryMS.MS93.V r.radical (alpha r.radical) →
      stabilizer r.radical (alpha r.radical)≤normalizer (Y:Set (FreeAmalgam r.radical)) →
      (¬Y≤B r.radical (alpha r.radical)
        (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.Z_normal _)) →
      H₁≤Z r.radical (alpha r.radical) → Nat.card H₁≤2 →
      (¬H₁≤centralizer (Z r.radical f:Set (FreeAmalgam r.radical))) →
      ⁅Y,T₀⁆≤H₁ →
      Z r.radical (p.walk.getVert (p.walk.length-2)) ⊔
        (Z r.radical e⊓Q r.radical (alpha r.radical))≤T₀ → False := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r e p hb f hf hef hpf Y T₀ H₁ hYV hYN hYB hHZ hcard hHf hcomm hinner
  exact source_not_alternatingBlock d h hU hV
    (SymplecticSetup.SourceData.reducedSource_block_of_shifted_controlled_line
      d0 hm r p hb f hf hef hpf Y T₀ H₁ hYV hYN hYB hHZ hcard hHf hcomm hinner)

/-- The actual original source excludes the controlled-line configuration at
every original-group vertex. -/
theorem sourceData_shifted_controlled_line_false_at
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v≠1) :
    let := component_normal d
    let := local_module_normal d
    let d0 := sourceData d h hU hV v hv
    ∀ (hm : IntrinsicMSPair d0)
      (r : CharacteristicReduction ((LX).subgroupOf (LX⊔d0.B))
        (d0.B.subgroupOf (LX⊔d0.B))) {a e : Vertex r.radical}
      (_ha : color r.radical a=false)
      (p : DistanceEight.PathCentrality.CriticalPath r.radical
        ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry a e),
      4<((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.b r.radical →
      ∀ f : Vertex r.radical, color r.radical f=false →
      (cosetGraph r.radical).dist e f≤2 →
      (cosetGraph r.radical).dist (p.walk.getVert (p.walk.length-2)) f≤4 →
      ∀ Y T₀ H₁ : Subgroup (FreeAmalgam r.radical),
      Y≤BinaryMS.MS93.V r.radical a →
      stabilizer r.radical a≤normalizer (Y:Set (FreeAmalgam r.radical)) →
      (¬Y≤B r.radical a
        (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.Z_normal _)) →
      H₁≤Z r.radical a → Nat.card H₁≤2 →
      (¬H₁≤centralizer (Z r.radical f:Set (FreeAmalgam r.radical))) →
      ⁅Y,T₀⁆≤H₁ →
      Z r.radical (p.walk.getVert (p.walk.length-2)) ⊔
        (Z r.radical e⊓Q r.radical a)≤T₀ → False := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r a e ha p hb f hf hef hpf Y T₀ H₁ hYV hYN hYB hHZ hcard hHf hcomm hinner
  exact source_not_alternatingBlock d h hU hV
    (SymplecticSetup.SourceData.reducedSource_block_of_shifted_controlled_line_at
      d0 hm r ha p hb f hf hef hpf Y T₀ H₁ hYV hYN hYB hHZ hcard hHf hcomm hinner)

end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann

