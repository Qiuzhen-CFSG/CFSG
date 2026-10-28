module
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentAutomizer
public import Theory.GroupTheory.NormalizerAction.Simple
public import Theory.Quasithin.NormalTwoQuotient
/-!
# The source component automizer is a core-free SQTK group

The literal component image is normal and has two-group quotient, so every
odd-prime rank equals that of the component. The K-group property passes
through the actual normalizer quotient. Faithfulness and simplicity make
its radical trivial, hence its minimal-parabolic core is trivial as well.
This reduces both the normal and the paired source cases to the same normal
simple-component family theorems without a new classification hypothesis.

Source: Aschbacher–Smith E.2.2, printed pp.215–216.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

omit [Finite H] in
private theorem simple_component_center {K : Subgroup H}
    (hK : IsComponent H K) [IsSimpleGroup K] : center K = ⊥ := by
  let := hK.2
  rcases (inferInstance : (center K).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp h)).elim

/-- The original component automizer inherits SQTK without an additional section-rank hypothesis. -/
theorem source_component_automizer_sqtk (hH : IsSQTK κ H)
    (T : Sylow 2 H) {K : Subgroup H} (hK : IsComponent H K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) : IsSQTK κ (NormalizerAction.Star K) := by
  have ho := generating_component_orbit_eq_residual hH.stronglyQuasithin T hK hgen
  let D := NormalizerAction.componentImage K
  let S := ((T : Subgroup H).subgroupOf (normalizer (K : Set H))).map (NormalizerAction.quotient K)
  have hDS : D ⊔ S = ⊤ := component_automizer_sylow_supplement T hK ho
  have hS : IsPGroup 2 S := T.isPGroup'.comap_subtype.map _
  have hq : IsPGroup 2 (NormalizerAction.Star K ⧸ D) := isPGroup_quotient_of_sup_eq_top D S hS hDS
  let e := NormalizerAction.componentEquivOfCenterEqBot K (simple_component_center hK)
  refine ⟨?_,(hH.isKGroup.subgroup (normalizer (K : Set H))).quotient (NormalizerAction.C K)⟩
  intro p hp hop
  let : Fact p.Prime := ⟨hp⟩
  calc
    primeRank p (NormalizerAction.Star K) ≤ primeRank p D := primeRank_le_of_normal_two_quotient D hq p hop
    _ = primeRank p K := (Theory.GroupTheory.primeRank_equiv p e).symm
    _ ≤ 2 := (primeRank_subgroup_le p K).trans (hH.stronglyQuasithin p hp hop)

/-- Every minimal parabolic on the literal simple-component automizer has trivial normal core. -/
theorem source_component_automizer_core {K : Subgroup H}
    (hK : IsComponent H K) [IsSimpleGroup K]
    (S : Sylow 2 (NormalizerAction.Star K)) (hPs : ChapterB.IsMinimalParabolicOver S ⊤) :
    ChapterB.minimalParabolicCore S hPs = ⊥ := by
  let := hK.2
  have hr := NormalizerAction.solvableRadical_star_eq_bot K (simple_component_center hK)
  have hs := ChapterB.minimalParabolic_core_solvable S hPs
  exact bot_unique ((le_solvableRadical _ inferInstance hs).trans hr.le)

/-- The actual paired-source reduction to a normal simple, core-free SQTK configuration. -/
theorem source_component_as_normal (hH : IsSQTK κ H)
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {K : Subgroup H} (hK : IsComponent H K) [IsSimpleGroup K]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    let A := NormalizerAction.Star K
    let D := NormalizerAction.componentImage K
    IsSQTK κ A ∧ Nonempty (K ≃* D) ∧ IsSimpleGroup D ∧ ¬ IsMulCommutative D ∧ D.Normal ∧
      ∃ S : Sylow 2 A, D ⊔ (S : Subgroup A) = ⊤ ∧
        ∃ hPs : ChapterB.IsMinimalParabolicOver S ⊤,
          ChapterB.minimalParabolicCore S hPs = ⊥ ∧
          ChapterB.minimalParabolicMax S hPs =
            ((ChapterB.minimalParabolicMax T hP).subgroupOf (normalizer (K : Set H))).map
              (NormalizerAction.quotient K) := by
  let D := NormalizerAction.componentImage K
  let e := NormalizerAction.componentEquivOfCenterEqBot K (simple_component_center hK)
  let := hK.2
  let : IsSimpleGroup D := e.symm.isSimpleGroup
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨S,hS,hPs,hM⟩ := source_component_automizer hH.stronglyQuasithin T hP hK hgen
  have ho := generating_component_orbit_eq_residual hH.stronglyQuasithin T hK hgen
  refine ⟨source_component_automizer_sqtk hH T hK hgen,⟨e⟩,inferInstance,
    Group.IsPerfect.not_isMulCommutative D,inferInstance,S,?_,hPs,
    source_component_automizer_core hK S hPs,hM⟩
  rw [hS]
  exact component_automizer_sylow_supplement T hK ho
end CFSG.Quasithin.ChapterE.Structure
