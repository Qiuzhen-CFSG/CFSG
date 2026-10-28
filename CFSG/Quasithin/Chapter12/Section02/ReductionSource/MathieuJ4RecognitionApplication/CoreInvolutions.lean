module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.Thompson
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.FullCubicSplitting

/-!
# The original Mathieu cubic-normalizer splitting

The original marked Mathieu arguments supply the elementary cocode
normalizer and its sextet marker. The extraspecial core maps onto the full
sextet two-core with elementary kernel of order 128; square correction and
native fusion lift every M24 involution through this original quotient.
An involutory scalar inverter then yields a complement to C_H(X) in N_H(X)
for every original cubic marking and Sylow choice. No extra premise or
LocalData-dependent fusion is used.

This proves the splitting clause of AS91 (4.9) for the actual original
Aschbacher--Smith 8.2.12--14 Mathieu inputs. Todd complements, construction
of general/native LocalData, and unconditional ambient recognition remain
separate obligations. Source: Aschbacher--Segev, Invent. Math. 105 (1991),
(4.8)--(4.9), p.599, DOI 10.1007/BF01232280.
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu MathieuCode Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Chapter8.Section02.Centralizer
open Recognition.JankoFour.SourceRecognition
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
variable (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1)
    (hquot : Nonempty (Recognition.JankoFour.CubicAutomorphismQuotient
      ((centralizer ({(z : G)} : Set G)) ⧸
        pCore 2 (centralizer ({(z : G)} : Set G)))))

include D h hmany hV hq hnon a E hE

include z hz hne hquot

/-- Every native M24 involution lifts through the original automizer map. -/
theorem sourceOrbit_m24_original_involution_lift (u : M24) (hu : orderOf u=2) :
    ∃ x : normalizer (D.sourceOrbit : Set G),
      a (D.sourceOrbit.normalizerMonoidHom.rangeRestrict x)=u ∧ orderOf x=2 := by
  have ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  let W := D.sourceOrbit
  let f := a.toMonoidHom.comp W.normalizerMonoidHom.rangeRestrict
  have hf : Function.Surjective f := a.surjective.comp W.normalizerMonoidHom.rangeRestrict_surjective
  have hc := sourceOrbit_m24_selfCentralizing D h hmany hV hq hnon a E hE z hz hne hquot
  have hk : f.ker = W.subgroupOf (normalizer (W : Set G)) := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,
      MonoidHom.ker_rangeRestrict,normalizerMonoidHom_ker,hc]
  have hF : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)) := by
    intro n v
    exact hE (W.normalizerMonoidHom.rangeRestrict n) (Additive.ofMul v)
  obtain ⟨S,hS⟩ := D.sourceOrbit_m24_central_sextet h hmany hV hq hnon a E hE z hz hne
  obtain ⟨cubic⟩ := ht.cubic_quotient
  exact marked_cocode_involution_lift W f hf hk E hF z S hS ht cubic u hu

/-- The original normalizer splits over its full cubic centralizer, with an
explicit involutory inverter and the original quotient marking retained. -/
theorem sourceOrbit_m24_full_cubic_split :
    ∀ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic)),
      ∃ v : fullCubicNormalizer cubic X, orderOf v=2 ∧
        v.val ∉ fullCubicCentralizer cubic X ∧
        (∀ x ∈ cubicSylowImage cubic X, v.val*x*v.val⁻¹=x⁻¹) ∧
        IsComplement' ((fullCubicCentralizer cubic X).subgroupOf (fullCubicNormalizer cubic X))
          (zpowers v) := by
  intro cubic X
  have ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  let W := D.sourceOrbit
  let f := a.toMonoidHom.comp W.normalizerMonoidHom.rangeRestrict
  have hf : Function.Surjective f := a.surjective.comp W.normalizerMonoidHom.rangeRestrict_surjective
  have hc := sourceOrbit_m24_selfCentralizing D h hmany hV hq hnon a E hE z hz hne hquot
  have hk : f.ker = W.subgroupOf (normalizer (W : Set G)) := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,
      MonoidHom.ker_rangeRestrict,normalizerMonoidHom_ker,hc]
  have hF : ∀ n v, E (Additive.ofMul (W.normalizerMonoidHom n v)) =
      cocodeRepresentation (f n) (E (Additive.ofMul v)) := by
    intro n v
    exact hE (W.normalizerMonoidHom.rangeRestrict n) (Additive.ofMul v)
  obtain ⟨S,hS⟩ := D.sourceOrbit_m24_central_sextet h hmany hV hq hnon a E hE z hz hne
  exact marked_fullCubicNormalizer_split W f hf hk E hF z S hS ht cubic X

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
