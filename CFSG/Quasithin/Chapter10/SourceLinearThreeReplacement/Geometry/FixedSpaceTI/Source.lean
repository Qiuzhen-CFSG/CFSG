module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.Intersections
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfSylow
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Assembly

/-!
# Assembly of fixed-space vanishing and TI from the remaining source bounds

The original multiple-overgroup guard selects H*. The two numerical module
bounds contradict the proved movement of the zeroth weak closure, giving
C_V(L₀)=1. The literal SL₃(2) residual argument then supplies the outside-M
intersections, using the independently owned half-Sylow uniqueness theorem.
The already proved pair action gives TI and feeds the centralizer geometry.

This is a conditional assembly: the two parameter inputs and half-Sylow
uniqueness must all be discharged before claiming source 10.3.1.
Source: Aschbacher--Smith 10.2.6,10.2.10 and10.3.1, pp.748--756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The numerical inputs suffice for fixed-space vanishing on the original setup. -/
theorem fixed_part_of_parameter_inputs
    (hs : GlobalSAt T) (ha : HStarLocalAAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D) :
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ := by
  by_contra hfix
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hout : Chapter3.HasMaximalOutside T D.maximalLocal := by
    obtain ⟨A,hA,B,hB,hne⟩ := (Set.one_lt_ncard_iff_nontrivial_and_finite.mp hmany).1
    by_cases hAM : A = D.maximalLocal
    · exact Chapter3.hasMaximalOutside_of_two_distinct hu.normalizer_maximal hB.1
        (le_normalizer_componentOrbit L T) hB.2 (fun he => hne (hAM.trans he.symm))
    · exact Chapter3.hasMaximalOutside_of_two_distinct hu.normalizer_maximal hA.1
        (le_normalizer_componentOrbit L T) hA.2 hAM
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
  obtain ⟨I,_hIU,hHI,hmove,hI,haI⟩ := ha hmany L D s hfix H hH
  let := hI
  exact false_of_moved_parameter_bounds D s hH.1.1.2 hHI hmove haI
    (hs hmany L D s hfix)

/-- Half-Sylow uniqueness removes the component-normalizer premise in the
actual linear-three outside-M intersection theorem. No fixed-space premise
is needed for this part. -/
theorem survivor_outside_intersection_of_halfSylow
    (hhalf : PointControl.HalfSylowUniqueAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreeSurvivor T D)
    {g : G} (hg : g ∉ D.maximalLocal) :
    ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥ := by
  have hn := survivor_nonnormal s
  have hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) := by
    rintro ⟨e⟩
    exact Matrix.PSL3Two.not_nonempty_alternatingFive_equiv
      ⟨e.symm.trans (s.quotient.trans Atlas.Comparisons.Exceptional.sl3TwoEquivPsl3Two)⟩
  exact moved_inf_conjugate_eq_bot D s.quotient hn s.exchange s.exchange_mem
    s.crossed s.pointCentralizers
    (PointControl.component_normalizer_le_of_halfSylowUnique D hn
      (hhalf hmany L D hn hnot)) hg

/-- Conditional assembly into the exact original fixed-space/TI contract. -/
theorem fixedSpaceTI_of_source_inputs
    (hs : GlobalSAt T) (ha : HStarLocalAAt T)
    (hhalf : PointControl.HalfSylowUniqueAt T) : FixedSpaceTIAt T := by
  intro hmany L D s
  have hz := fixed_part_of_parameter_inputs hs ha hmany D s
  exact ⟨hz,survivor_moved_ti_of_fixed_of_outside s hz
    (fun _ hg => survivor_outside_intersection_of_halfSylow hhalf hmany D s hg)⟩

/-- Application to the parent geometry, retaining its independent core and escape inputs. -/
theorem centralizerGeometry_of_parameter_inputs
    (hs : GlobalSAt T) (ha : HStarLocalAAt T)
    (hhalf : PointControl.HalfSylowUniqueAt T)
    (hcore : CoreReducedAt T) (hescape : EscapeAt T) : CentralizerGeometryAt T :=
  centralizerGeometry_of_source_inputs
    (fixedSpaceTI_of_source_inputs hs ha hhalf) hcore hescape

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI
