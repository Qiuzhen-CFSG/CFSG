module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.Thompson
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.FullCubicPerfect

/-!
# The original Mathieu application of AS91 (4.9) perfectness

The original automizer and cocode markings, together with the constructed
central sextet and self-centralizing kernel, supply the literal commutator
witness in C_H(X). For every original cubic quotient and every original
Sylow X, the full centralizer is perfect, quasisimple, and equal to its layer;
its center has order six. No splitting or local-geometry package is an input.

The involution needed for the other clause of (4.9), Todd splitting, the
general/native LocalData constructors and ambient recognition remain open.
Source: Aschbacher--Segev, The uniqueness of groups of type J4,
Invent. Math. 105 (1991), (4.9), p.599, DOI 10.1007/BF01232280;
Aschbacher--Smith 8.2.12--14, original marked Mathieu application.
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

/-- The original marked Mathieu data prove the perfectness clause of AS91
(4.9) for EVERY original cubic quotient and Sylow three-subgroup. -/
theorem sourceOrbit_m24_full_cubic_perfect :
    ∀ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic)),
      fullCubicMarker cubic X ∈ commutator (fullCubicCentralizer cubic X) ∧
      Group.IsPerfect (fullCubicCentralizer cubic X) ∧
      componentLayer (fullCubicCentralizer cubic X) = ⊤ ∧
      IsQuasisimple (fullCubicCentralizer cubic X) ∧
      Nat.card (center (fullCubicCentralizer cubic X)) = 6 := by
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
  have hp := marked_fullCubicCentralizer_perfect W f hf hk E hF z S hS ht cubic X
  have hl := marked_fullCubicCentralizer_layer W f hf hk E hF z S hS ht cubic X
  exact ⟨(fullCubicCentralizer_layer_eq_top_iff ht cubic X).mp hl,hp,hl,
    marked_fullCubicCentralizer_quasisimple W f hf hk E hF z S hS ht cubic X,
    fullCubicCentralizer_center_card ht cubic X⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
