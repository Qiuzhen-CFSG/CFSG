module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.HexadElementary
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.MarkedHexad

/-!
# The split hexad quotient at the original Mathieu overlap

The general source construction is identified with the original cocode
subgroup using its proved maximum elementary order in the full normalizer.
Consequently this same E is the original Thompson subgroup and has the
original component as its full ambient normalizer. In the literal overlap
quotient, Q has elementary image of order 64 and a complementary normalizer
image of order 2160. Its native six-letter action is surjective with kernel
exactly the image of the original cubic Sylow subgroup.

Source: Aschbacher–Segev (4.6), Invent. Math. 105 (1991), p.598,
DOI 10.1007/BF01232280; Aschbacher–Smith 8.2.12–14. The original marked
Mathieu hypotheses are retained. General unmarked Thompson equality and
normalizer recognition are separate remaining source obligations.
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

/-- Identify the source construction with the original cocode and retain
the literal split quotient, six-letter action and cubic kernel. -/
theorem sourceOrbit_m24_hexad_quotient :
    let ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
    ∀ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic)),
      ∃ B, ∃ hB : B ∈ m22Blocks,
        let I := (normalizer (D.sourceOrbit : Set G)).subgroupOf
          (centralizer ({(z : G)} : Set G))
        let F := originalHexadElementary ht cubic X B
        letI := originalHexadElementary_normal ht cubic X hB
        let q := QuotientGroup.mk' (F.subgroupOf (originalPlaneHexad cubic B))
        let Qbar := ((Recognition.JankoFour.core (z : G)).subgroupOf
          (originalPlaneHexad cubic B)).map q
        let Nbar := ((originalHexadNormalizer cubic X B).subgroupOf
          (originalPlaneHexad cubic B)).map q
        I = originalPlaneHexad cubic B ∧
        F.map (centralizer ({(z : G)} : Set G)).subtype = D.sourceOrbit ∧
        F.map (centralizer ({(z : G)} : Set G)).subtype = elementaryAbelianMaxJ (T : Subgroup G) ∧
        normalizer (F.map (centralizer ({(z : G)} : Set G)).subtype : Set G) = L ∧
        Qbar.IsComplement' Nbar ∧ IsElementaryAbelian 2 Qbar ∧
        Nat.card Qbar = 64 ∧ Nat.card Nbar = 2160 ∧
        Function.Surjective (originalHexadComplementProjection ht cubic X hB) ∧
        Nat.card (originalHexadComplementProjection ht cubic X hB).ker = 3 ∧
        (originalHexadComplementProjection ht cubic X hB).ker.map Nbar.subtype =
          ((cubicSylowImage cubic X).subgroupOf (originalPlaneHexad cubic B)).map q := by
  intro ht cubic X
  obtain ⟨B,hB,hpre,_⟩ := D.sourceOrbit_m24_hexad_elementary
    h hmany hV hq hnon a E hE z hz hne hquot cubic X
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
  have heq := marked_hexadElementary_eq W f hf hk E hF ht cubic X hB hpre
  refine ⟨B,hB,hpre,heq,?_,?_,originalHexadQuotient_split ht cubic X hB,
    (originalHexadQuotient_core_data ht cubic X hB).1,
    (originalHexadQuotient_core_data ht cubic X hB).2,
    originalHexadQuotient_normalizer_card ht cubic X hB,
    originalHexadComplementProjection_surjective ht cubic X hB,
    originalHexadComplementProjection_kernel_card ht cubic X hB,
    originalHexadComplementProjection_kernel ht cubic X hB⟩
  · exact heq.trans (D.sourceOrbit_m24_thompson_eq
      h hmany hV hq hnon a E hE z hz hne hquot).symm
  · rw [heq]
    exact D.sourceOrbit_m24_normalizer_eq_component h hmany hV hq hnon a E hE z hz hne hquot

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
