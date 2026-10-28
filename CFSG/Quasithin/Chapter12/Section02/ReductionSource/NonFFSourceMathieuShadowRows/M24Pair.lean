module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Pair
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Pair
public import CFSG.Quasithin.ChapterE.Section04.MathieuBounds.SmallQuotients

/-!
# Original pair selection for both M24 rows

The full original automizer marking gives a ≤ 3 and m ≥ 4. The literal
weak-closure inequality m ≤ w + a therefore gives positive w. Apply the
original H-star two-core escape and E.2 witness constructor to choose the
pair in that same H, with its internal conjugator, whole two-core quotient,
Sylow intersection and geometric marking. Both code and cocode are retained.

The private import intentionally continues the M24 pair implementation;
its positive-w constructor is reused without changing the existing cocode
three-space API. The later degree-one and code exclusion arguments are separate.
Source: Aschbacher--Smith 7.3.3 and 8.2.2, printed pp.699,714--715.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu MathieuCode
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction

private theorem m24_cocode_involution_four (a : M24) (ha : orderOf a = 2) :
    4 ≤ fixedCodim cocodeRepresentation (zpowers a) := by
  rcases M24InvolutionCentralizers.involution_classes a ha with hz | ht
  · rw [CocodeOctad.Involutions.fixedCodim_of_isConj_z a hz]
  · rw [CocodeOctad.Involutions.fixedCodim_of_isConj_t a ht]
    decide

private theorem m24_marked_parameters
    {X E : Type*} [Group X] [Finite X] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (ρ : Representation (ZMod 2) X E)
    (hm : MathieuSmall.IsM24ToddOrDual ρ) : moduleA ρ ≤ 3 ∧ 4 ≤ moduleM ρ := by
  obtain ⟨a,hc | hd⟩ := hm
  · obtain ⟨F⟩ := hc
    have he (g : X) (v : E) := LinearMap.congr_fun (F.isIntertwining' g) v
    refine ⟨(moduleA_le_of_equivariant_injective ρ cocodeRepresentation
      a.toMonoidHom a.injective F.toLinearEquiv he).trans
      ValueBound.MathieuBounds.moduleA_m24Cocode_le_three, ?_⟩
    apply le_csInf ⟨_, Set.mem_insert _ _⟩
    rintro d (rfl | ⟨t,ht,rfl⟩)
    · rw [F.toLinearEquiv.finrank_eq,finrank_cocode]
      decide
    · rw [fixedCodim_map_equivariant ρ cocodeRepresentation a.toMonoidHom
        F.toLinearEquiv he,MonoidHom.map_zpowers]
      exact m24_cocode_involution_four _ ((a.orderOf_eq t).trans ht)
  · obtain ⟨F⟩ := hd
    have he (g : X) (v : E) := LinearMap.congr_fun (F.isIntertwining' g) v
    refine ⟨(moduleA_le_of_equivariant_injective ρ codeRepresentation
      a.toMonoidHom a.injective F.toLinearEquiv he).trans
      ValueBound.MathieuBounds.moduleA_m24Code_le_three, ?_⟩
    apply le_csInf ⟨_, Set.mem_insert _ _⟩
    rintro d (rfl | ⟨t,ht,rfl⟩)
    · rw [F.toLinearEquiv.finrank_eq,finrank_code]
      decide
    · rw [fixedCodim_map_equivariant ρ codeRepresentation a.toMonoidHom
        F.toLinearEquiv he,MonoidHom.map_zpowers,code_cocode_fixedCodim_zpowers]
      exact m24_cocode_involution_four _ ((a.orderOf_eq t).trans ht)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Source 7.3.3 gives positive weak closure for either original M24 module. -/
theorem sourceOrbit_m24_globalW_pos_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    0 < globalW D.sourceOrbit (T : Subgroup G) := by
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inr (Or.inr (Or.inr hq))
  obtain ⟨ha,hm4⟩ := m24_marked_parameters (automizerRepresentation D.sourceOrbit)
    (D.sourceOrbit_m24_automizer_marking h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) hq)
  apply globalW_pos_of_local_parameter_gap D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_mathieu_initial_parameters h hmany hV hm hnon).1
  exact lt_of_le_of_lt ha (lt_of_lt_of_le (by decide : (3 : ℕ∞) < 4)
    (ENat.natCast_le_natCast.mpr hm4))

/-- Source 8.2.2 selects an actual pair inside every original M24 H-star,
with no positive-parameter or assumed-pair premise. -/
theorem sourceOrbit_m24_geometric_pair_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (k : ℕ) (i : I) (S : Sylow 2 I),
      GeometricSelected H T (normalizer (L : Set G)) D.sourceOrbit I k i S :=
  D.sourceOrbit_m24_geometric_pair_of_positive h hmany hV hq hnon hH
    (D.sourceOrbit_m24_globalW_pos_of_many h hmany hV hq hnon)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
