module
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.NaturalLocalAction.LongRootModuleSource
public import Theory.SpecificGroups.G2.CoverFixedNaturalSections.RootCentralizer
public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts.CentralizerCore.Containment
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.InvolutionConjugacy
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.PureLong

/-!
# Discharging the universal G2 geometry in the marked J2 exclusion

The actual root-conjugacy theorem, full long-root centralizer, short-root
centralizer containment and pure-long fusion provide all four B.4.6 root
clauses. A subgroup all of whose nonidentity elements are long-root elements
has exponent two and is elementary abelian, so the proved elementary fusion
applies. The independent long-root pointwise-fixer theorem supplies the
natural-module clauses. Thus the existing no-FF calculation now applies to
every genuine marked J2 module without additional root-geometry premises.

Source: Aschbacher--Smith B.4.6(4)--(6),(11), printed pp.88--89;
K.4.5, printed p.460.
-/

public noncomputable section
open Subgroup Atlas.G2
namespace CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction

/-- All four literal earlier-source root clauses hold over every finite even field. -/
theorem b46RootFacts (K : Type*) [Field K] [CharP K 2] [Finite K] :
    InvolutionImages.B46RootFacts K := by
  constructor
  · intro x hx hn
    exact EvenInvolutionGeometry.involution_isRoot hx hn
  · intro r hr
    exact LieParabolicSetup.centralizer_rootA_eq_local₁ hr
  · intro r hr
    exact ShortRootProducts.CentralizerCore.centralizer_rootC_le_parabolic r hr
  · intro B hB
    have hsquare (b : B) : b ^ 2 = 1 := by
      apply Subtype.ext
      change (b : Model K) ^ 2 = 1
      by_cases hb : (b : Model K) = 1
      · rw [hb, one_pow]
      obtain ⟨g,r,hr,he⟩ := hB b b.property hb
      rw [he, ← map_pow, pow_two, rootA_add, CharTwo.add_self_eq_zero, rootA_zero, map_one]
    have hinv (b : B) : b⁻¹ = b :=
      inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hsquare b)
    let : IsElementaryAbelian 2 B := {
      toIsMulCommutative := IsMulCommutative.of_comm fun a b => by
        calc
          a * b = (a * b)⁻¹ := (hinv (a*b)).symm
          _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
          _ = b * a := by rw [hinv, hinv]
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare }
    apply EvenInvolutionGeometry.PureLong.exists_map_le_longRootLocal B inferInstance
    intro b hb hn
    obtain ⟨g,r,hr,he⟩ := hB b hb hn
    exact ⟨r,hr,g,he⟩

end CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction

namespace CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
open Representation Representation.BinaryOffender NaturalLocalAction
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- A genuine marked module for the actual four-element field has no FF offender. -/
theorem not_isFFModule_four
    (D : MarkedModule (K := Sporadic.LeechRelated.J2.G2FourModule.F) ρ) :
    ¬ IsFFModule ρ :=
  D.not_isFFModule (b46RootFacts _) b46LongRootModuleFacts_four

end CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
