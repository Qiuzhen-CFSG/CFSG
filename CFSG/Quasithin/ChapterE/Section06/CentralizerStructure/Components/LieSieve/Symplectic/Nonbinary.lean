module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Carrier
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Nonbinary.Reduction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Nonbinary.Intersection
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Nonbinary.Escape

/-!
# Nonbinary symplectic component actions in E.6.8(2)

The displacement [V,L ∩ M] is one of the two central root subgroups or
the full central root plane in an actual symplectic matrix model. Its
normalizer is L ∩ M. The root cases give maximal parabolics, corank n,
and the literal root conjugation action on Sp₄(F)′. The full-plane case
gives the Borel, corank 2n, and the strict intermediate subgroup with
an escaping centralizer. The displacement decomposition and the upper
corank bound retain the precise source actors.

`Nonbinary.alternative` proves the conditional task contract. The existence
of a Borel inside L ∩ M and universal diagram-preserving semilinear coverage
remain explicit; the parent symplectic assembly must supply them.

Source: Aschbacher–Smith, E.6.8(2), printed pp.247–248 (PDF pp.258–259).
-/

public section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.Nonbinary
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G} {n : ℕ}

/-- The complete nonbinary symplectic alternative, conditional on the independently
supplied Borel witness and universal diagram-preserving semilinear coverage. -/
theorem alternative
    (hclass : DiagramSemilinearCoverage)
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 1 < n) (hm : SymplecticDerivedModel L n)
    (hB : ∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B) :
    SymplecticAlternative M V U L n := by
  refine ⟨hm, fixedSpace_corank_le hU.1 hL.1,
    fun _ => decomposition hclass h hU hL hn hm hB, ?_⟩
  obtain ⟨F, _, _, _, hF, e, _, _, hcases⟩ :=
    exists_displacement_realization hclass h earlier hU hL hn hm hB
  have hJ := intersection_image_eq_normalizer hclass h hU hL hn hm hB e
  rcases hcases with hroot | hroot | hplane
  · refine Or.inr ⟨maximalParabolic_of_intersection_image hB hn hm e ?_,
      rootAction_of_displacement_image hclass h hU hL hn hm hB hF e 0 hroot,
      actionCorank_of_root_image hclass h hU hL hn hm hB hF e 0 hroot⟩
    rw [hJ, hroot, RootNormalizerResidual.normalizer_zero_eq]
    exact BorelActionGeometry.pointParabolic_isCoatom
  · refine Or.inr ⟨maximalParabolic_of_intersection_image hB hn hm e ?_,
      rootAction_of_displacement_image hclass h hU hL hn hm hB hF e 4 hroot,
      actionCorank_of_root_image hclass h hU hL hn hm hB hF e 4 hroot⟩
    rw [hJ, hroot, RootNormalizerResidual.normalizer_four_eq]
    exact BorelActionGeometry.planeParabolic_isCoatom
  · rw [hplane, BorelActionGeometry.normalizer_centralPlane_eq_borel] at hJ
    exact Or.inl ⟨borelPreimage_of_intersection_image hn hm hF e hJ, Or.inl
      ⟨actionCorank_of_centralPlane_image hclass h hU hL hn hm hB hF e hplane,
        centralPlane_escape hclass h hU hL hn hm hB hF e hplane hJ⟩⟩

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.Nonbinary
