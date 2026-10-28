module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeDegree
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelection

/-!
# The original M24 code offender

The degree-one pair attains the positive weak-closure minimum. The actual
two-core actor therefore equals the full offender normalizer, with its
original centralizer kernel. No offender, kernel or Sylow-placement premise
is added to the Chapter12 inputs.
Source: Aschbacher--Smith 8.2.2--3, printed pp.714--716.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original M24 code has w = 1; the same selected conjugator supplies
the full offender and preserves its literal two-core and centralizer kernel. -/
theorem sourceOrbit_m24_code_offender_pair_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      globalW D.sourceOrbit (T : Subgroup G) = 1 ∧
      IsWOffenderAt D.sourceOrbit T i.val⁻¹ ∧
      offenderNormalizer D.sourceOrbit i.val⁻¹ =
        D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype ∧
      offenderNormalizer D.sourceOrbit i.val⁻¹ ≤ T ∧
      offenderNormalizer D.sourceOrbit i.val⁻¹ ⊓ centralizer (D.sourceOrbit : Set G) =
        D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      ⁅⁅⁅D.sourceOrbit, offenderNormalizer D.sourceOrbit i.val⁻¹⁆,
        offenderNormalizer D.sourceOrbit i.val⁻¹⁆, offenderNormalizer D.sourceOrbit i.val⁻¹⁆ = ⊥ := by
  obtain ⟨I,i,S,s⟩ := D.sourceOrbit_m24_code_pair_degree_one_of_many
    h hmany hV hq hnon a E hE hH
  let s' := s.toSelected (one_dvd _)
  have hpos := D.sourceOrbit_m24_globalW_pos_of_many h hmany hV hq hnon
  obtain ⟨hw,hOff,hA,hAT,hker⟩ := selected_offender_of_parameter_bound s'
    D.sourceOrbit_weakClosure_setup (Order.one_le_iff_pos.mpr hpos)
  have hc := selected_actor_cubic I (normalizer (L : Set G)) D.sourceOrbit
    (s.generate ▸ le_sup_left) S i s.twoConjugate
  rw [← hA] at hc
  exact ⟨I,i,S,s',hw,hOff,hA,hAT,hker,hc⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
