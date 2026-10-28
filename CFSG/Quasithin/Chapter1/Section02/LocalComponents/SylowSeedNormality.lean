module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralNormality
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# Normality of a component containing a Sylow-invariant seed

In the two-core quotient a nonnormal C-component is quasisimple by the
noncentral-component normality theorem. The original ordinary-component
calculation makes it centerless. Distinct C-components commute, so a
subgroup surviving the two-core can lie in at most this one component.
Sylow invariance of that subgroup then gives component normality from
the source orbit bound. All universal A/C inputs use KnownSimple.

Source: Aschbacher–Smith, 1.2.1(3), p.504; application13.7.5(1), p.938.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The source C-component normality criterion, with the complete earlier source inputs discharged. -/
theorem cComponent_normal_of_sylow_invariant_seed
    (hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G))
    (S : Sylow 2 G) {K X : Subgroup G} (hK : K.IsCComponent)
    (hXK : X ≤ K) (hSX : (S : Subgroup G) ≤ normalizer (X : Set G))
    (hX : ¬ X ≤ pCore 2 G) : K.Normal := by
  classical
  by_contra hn
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  let : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
  have hB : B.IsCComponent := hK.map_quotient (pCore 2 G)
  have hnB : ¬ B.Normal := fun hb => hn (cComponent_normal_of_quotient_normal hK (pCore 2 G) hb)
  have hsimple : IsQuasisimple B :=
    (ChapterA.Section03.NoncentralNormality.normal_or_quasisimple hQ
      (pCore_quotient_pCore_eq_bot 2) hB).resolve_left hnB
  let := hsimple
  have hf : fittingSubgroup B ≤ center B :=
    (le_solvableRadical _ inferInstance inferInstance).trans IsQuasisimple.solvableRadical_le_center
  have hm := (ChapterA.SQTKStructure.ordinary_model_of_central_fitting
    (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
    (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y)) hQ B hB hf).2
  have hcomp : IsComponent (G ⧸ pCore 2 G) B := ⟨hB.subnormal, hsimple⟩
  have hz := ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.center_eq_bot_of_model
    (hQ.stronglyQuasithin 3 (by decide) (by decide))
    (pCore_quotient_pCore_eq_bot 2) B hcomp hnB hm
  have hu : ∀ D : Subgroup G, D.IsCComponent → X ≤ D → D = K := by
    intro D hD hXD
    by_contra hne
    let E := D.map q
    have hE : E.IsCComponent := hD.map_quotient (pCore 2 G)
    have hBE : B ≠ E := fun he => hne
      (hD.eq_of_map_quotient_eq hK (pCore 2 G) he.symm)
    have hc : B ≤ centralizer (E : Set (G ⧸ pCore 2 G)) :=
      commutator_eq_bot_iff_le_centralizer.mp
        (ChapterA.Section03.CComponentCommutation.commutator_eq_bot hQ
          (pCore_quotient_pCore_eq_bot 2) hB hE hBE)
    apply hX
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    let b : B := ⟨q x, mem_map_of_mem q (hXK hx)⟩
    have hb : b ∈ center B := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      exact (hc y.property (q x) (mem_map_of_mem q (hXD hx))).symm
    rw [hz] at hb
    exact congrArg Subtype.val (mem_bot.mp hb)
  exact hn (cComponent_normal_of_unique_of_orbit_two hK hXK hu S hSX
    (proposition_1_2_1_three_orbit_source hQ hK))

end CFSG.Quasithin.Chapter1.Section02
