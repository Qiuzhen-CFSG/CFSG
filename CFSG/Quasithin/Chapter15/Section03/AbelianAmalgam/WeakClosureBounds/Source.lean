module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.ModuleSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.SeedSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Normal.Source
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.OriginalModule.Exchanged.Source
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Source49.Original

/-!
# The original rank-two conclusion in the abelian-span case

Finite descent selects one minimal outside subgroup inside Mc. The genuine
E.2 model reduction either supplies generation one directly or gives an
odd-field component. Original 15.3.64 supplies the common quadratic actor.
The normal and exchanged module calculations contradict the latter case
on the literal seed. Original 15.3.63 then forces globalR(V)=2.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.63–65, printed pp.1151–1152.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.OriginalSource
open ChapterA.Section05To06 ChapterE GenerationOne
variable {G : Type*} [Group G] [Finite G]

theorem generation_one_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    [IsMulCommutative (conjugateSpanBy d.V d.Mc)]
    {H : Subgroup G} (hH : H ∈ minimalSylowOutsideFamily d.T d.M) (hHMc : H ≤ d.Mc) :
    IsEGenerated 1 H := by
  have hthree := Nat.prime_three.coprime_iff_not_dvd.mp
    (FusionCore.CosetSetup.Source49.intersection_three_prime_from_original
      hG d hempty hM hu hmany hfixed hHMc)
  rcases OriginalBorel.source_generation_one_or_odd_model
    hG d hempty hM hu hmany hH hthree with he | ⟨K,f,model⟩
  · exact he
  · exfalso
    obtain ⟨hP,hSQTK⟩ := OriginalBorel.source_minimal_parabolic hG d hempty hM hu hmany hH
    have h49 := (FusionCore.CosetSetup.Source49.ordinary_from_original
      hG d hempty hM hu hmany hfixed).1
    obtain ⟨hU,a,B,hB,hA,hq,hc⟩ := bounded_action_from_original
      hG d hempty hM hu hmany hfixed h49 hH.prop hHMc
    let := hU
    apply false_of_original_borel_calculation hG d hempty hM hu hmany hH hHMc model a
      (FusionCore.CosetSetup.Source49.intersection_residual_centralizes_from_original
        hG d hempty hM hu hmany hHMc)
    by_cases hn : K.Normal
    · exact OriginalModule.Normal.original_borel_calculation hH.prop.1.2 hP hSQTK
        a model hn hthree B hB hA hq hc
    · exact OriginalModule.Exchanged.local_commutator_borel_fixed hH hP hSQTK
        a K f model hn B hB hA hq hc

/-- Original 15.3.65(2), with earlier 45 and 50 retained as independent source
inputs on this same local datum. -/
theorem globalR_eq_two_from_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hfixed : centralizer (fixedPlane d.V₁ d.S : Set G) ≤ d.M)
    [IsMulCommutative (conjugateSpanBy d.V d.Mc)] : globalR d.V = 2 := by
  let := d.action.elementary
  obtain ⟨H,hHMc,hH⟩ := exists_minimal_outside_le_partner_from_original
    hG d hempty hM hu hmany
  exact globalR_eq_two_of_original_generation_one hG d hempty hM hu hmany hfixed
    ⟨H,hH.prop,generation_one_from_original hG d hempty hM hu hmany hfixed hH hHMc⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.OriginalSource
