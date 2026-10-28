module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardKernel
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann.Coordinates
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.BlockChiefCount

/-!
# The forward kernel of the original Baumann source

The original chief-count obstruction removes the block alternative. For each
actual characteristic replacement, an index-two forward moving intersection
therefore supplies the normalized starting kernel and its commutator line in
the common edge seed. This is the original Chapter 13 application of the
kernel preparation in MS93 (5.9), printed pp.920--922, used in
Aschbacher--Smith 13.7.4(1) through C.1.37.
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

/-- The normalized hyperplane kernel and its actual edge-seed commutator. -/
theorem sourceData_forward_kernel
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (v : V₁) (hv : v ≠ 1) :
    let := component_normal d
    let := local_module_normal d
    let d0 := sourceData d h hU hV v hv
    ∀ (hm : IntrinsicMSPair d0)
      (r : CharacteristicReduction ((LX).subgroupOf (LX⊔d0.B))
        (d0.B.subgroupOf (LX⊔d0.B))) (a c t : Vertex r.radical),
      color r.radical a = false → color r.radical c = false →
      Adjacent r.radical a t → Adjacent r.radical c t →
      2 < ((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.b r.radical →
      (B r.radical a (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.Z_normal _)).relIndex
        (U r.radical c) ≤ 2 →
      let T₀ := Q r.radical a ⊓ centralizer
        (U r.radical c ⊓ B r.radical a
          (((SymplecticSetup.SourceData.originalSource d0 hm).reduce r).geometry.Z_normal _) :
            Set (FreeAmalgam r.radical))
      stabilizer r.radical a ≤ normalizer (T₀ : Set (FreeAmalgam r.radical)) ∧
      Nat.card (⁅U r.radical c,T₀⁆ : Subgroup (FreeAmalgam r.radical)) ≤ 2 ∧
      ⁅U r.radical c,T₀⁆ ≤ Z r.radical t := by
  let := component_normal d
  let := local_module_normal d
  let d0 := sourceData d h hU hV v hv
  dsimp only
  intro hm r a c t ha hc hat hct hb hindex
  rcases SymplecticSetup.SourceData.reducedSource_block_or_forward_kernel
    d0 hm r ha hc hat hct hb hindex with hblock|hk
  · exact (source_not_alternatingBlock d h hU hV hblock).elim
  · exact hk

end CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalBaumann
