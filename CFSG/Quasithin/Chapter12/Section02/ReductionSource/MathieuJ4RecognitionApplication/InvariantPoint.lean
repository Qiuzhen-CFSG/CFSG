module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.ToddSplitting
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint.Hexad

/-!
# Constructing the invariant elementary preimage in the original Mathieu branch

The original marked Mathieu data construct the order-2160 actor J, its
native hexad section and its compatible outer involution. Both generators
fix the same point through the original cubic projection. Pulling back
the native singular point space constructs an actual elementary P of
order 128 inside Q, containing the central marker and normalized by J.
No elementary-preimage or invariance premise is assumed.

For these same J and P, the existing Todd splitting proof now requires
only that P meet the original Q intersect E in the marker line. The
consumer below retains that exact remaining intersection, while preserving
both original cocode and quotient markings on the resulting Todd map.
This is not unconditional PointData or J4 recognition.

Source: Aschbacher--Segev (4.8), Invent. Math. 105 (1991), p.599,
DOI 10.1007/BF01232280; the original Aschbacher--Smith 8.2.12--14 application.
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

/-- Construct an elementary order-128 preimage invariant under the actual
hexad actor. Only its displayed intersection remains for the Todd constructor. -/
theorem sourceOrbit_m24_pointData_intersection_reduction :
    ∀ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic)),
      ∃ J P : Subgroup (centralizer ({(z : G)} : Set G)),
        Nat.card J=2160 ∧ cubicSylowImage cubic X ≤ J ∧
        J ≤ fullCubicNormalizer cubic X ∧
        J ≤ (normalizer (D.sourceOrbit : Set G)).subgroupOf (centralizer ({(z : G)} : Set G)) ∧
        Disjoint (D.sourceOrbit.subgroupOf (centralizer ({(z : G)} : Set G)) ⊔
          Recognition.JankoFour.core (z : G)) J ∧
        IsElementaryAbelian 2 P ∧ P ≤ Recognition.JankoFour.core (z : G) ∧
        Nat.card P=128 ∧ center (centralizer ({(z : G)} : Set G)) ≤ P ∧
        J ≤ normalizer (P : Set (centralizer ({(z : G)} : Set G))) ∧
        ((D.sourceOrbit.subgroupOf (centralizer ({(z : G)} : Set G)) ⊓
            Recognition.JankoFour.core (z : G)) ⊓ P = center (centralizer ({(z : G)} : Set G)) →
          ∃ data : Recognition.JankoFour.LocalGeometry.LocalSubgroups.PointData (z : G),
            data.cubic=cubic ∧ ∃ hm : data.M=normalizer (D.sourceOrbit : Set G),
              (∀ x, a (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
                (MulEquiv.subgroupCongr hm (data.toddEquiv x)))=x.right) ∧
              (∀ w : D.sourceOrbit,
                (data.toddEquiv (SemidirectProduct.inl
                  (Multiplicative.ofAdd (E (Additive.ofMul w))))).val=w.val)) := by
  intro cubic X
  have ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨B,hB,hpre,A,v,t,hAc,_,_,him,_,_,_,htp,hvt,hv,hvo,hvA,hJc,_,_,hJN,hXJ,hJM⟩ :=
    D.sourceOrbit_m24_full_cubic_hexad_outer h hmany hV hq hnon a E hE z hz hne hquot cubic X
  let J := A.map (fullCubicCentralizer cubic X).subtype ⊔ zpowers v.val
  let C := centralizer ({(z : G)} : Set G)
  let W := D.sourceOrbit
  let W0 := W.subgroupOf C
  let N := W0 ⊔ Recognition.JankoFour.core (z : G)
  have hW0 : IsPGroup 2 W0 :=
    (IsElementaryAbelian.isPGroup (p := 2) (G := W)).comap_subtype
  let := ht.extraspecial
  have hN : IsPGroup 2 N := hW0.to_sup_of_normal_right
    (IsExtraspecial.isPGroup 2 (Recognition.JankoFour.core (z : G)))
  have hJW : J ≤ normalizer (W0 : Set C) :=
    hJM.trans (Subgroup.le_normalizer_comap C.subtype)
  have hJnorm : J ≤ normalizer (N : Set C) :=
    (le_inf hJW le_normalizer_of_normal).trans
      (normalizer_inf_normalizer_le_normalizer_sup W0 (Recognition.JankoFour.core (z : G)))
  have hdis := fullCubic_hexad_disjoint_normal_two ht cubic X hB A hAc him v hv hvo hvA N hN hXJ hJnorm
  obtain ⟨P,hPQ,hP,hPc,hZP,hJP⟩ := InvariantPoint.hexad_actor_invariant_preimage ht cubic X
    hB A him v t htp hvt
  refine ⟨J,P,hJc,hXJ,hJN,hJM,hdis,hP,hPQ,hPc,hZP,hJP,?_⟩
  intro hEP
  let := hP
  let f := a.toMonoidHom.comp W.normalizerMonoidHom.rangeRestrict
  have hf : Function.Surjective f := a.surjective.comp W.normalizerMonoidHom.rangeRestrict_surjective
  have hc := sourceOrbit_m24_selfCentralizing D h hmany hV hq hnon a E hE z hz hne hquot
  have hk : f.ker = W.subgroupOf (normalizer (W : Set G)) := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,
      MonoidHom.ker_rangeRestrict,normalizerMonoidHom_ker,hc]
  have hF : ∀ n w, E (Additive.ofMul (W.normalizerMonoidHom n w)) =
      cocodeRepresentation (f n) (E (Additive.ofMul w)) := by
    intro n w
    exact hE (W.normalizerMonoidHom.rangeRestrict n) (Additive.ofMul w)
  obtain ⟨S,hS⟩ := D.sourceOrbit_m24_central_sextet h hmany hV hq hnon a E hE z hz hne
  obtain ⟨equiv,heq,hew⟩ := marked_cocode_todd_of_invariant_preimage W f hf hk E hF z S hS ht
    cubic X J P hJc hXJ hJN hJM hdis hPQ hPc hEP hJP
  let data : Recognition.JankoFour.LocalGeometry.LocalSubgroups.PointData (z : G) := {
    cubic := cubic
    M := normalizer (W : Set G)
    toddEquiv := equiv
    hexad := B
    hexad_mem := hB
    overlap := hpre }
  exact ⟨data,rfl,rfl,heq,hew⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
