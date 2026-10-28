module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.MathieuJ4RecognitionApplication.HexadOuterComplement
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ToddSplitting

/-!
# Reducing the original Mathieu PointData constructor to one invariant preimage

The original marked Mathieu inputs construct the order-2160 hexad actor J
in the actual point-plane overlap. Its original cubic, normalizer placement,
and disjointness from E Q are proved without extra inputs. For that same J,
an elementary order-128 subgroup P of Q, meeting Q intersect E exactly in
the marker line and normalized by J, yields a complement in the overlap.
Gaschütz and the literal cocode action then give ToddGroup equivalent to
N_G(E) and construct PointData with the original cubic and native hexad.
Both the cocode inclusion and the original M24 quotient are retained.

This is a conditional constructor reduction, not the existence of P or an
unconditional PointData or J4-recognition theorem. Constructing P from the
source module remains with this recognition family. No LocalData-dependent
fusion or no_J4 premise is used.

Source: Aschbacher--Segev, Invent. Math. 105 (1991), (4.8), printed
pp.598--599, DOI 10.1007/BF01232280; Aschbacher--Smith 8.2.12--14.
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

/-- The original overlap supplies an actual order-2160 actor avoiding E Q.
For this actor, the displayed elementary invariant preimage suffices to
construct PointData and a Todd isomorphism preserving both original maps. -/
theorem sourceOrbit_m24_pointData_invariant_preimage_reduction :
    ∀ (cubic : Recognition.JankoFour.CubicAutomorphismQuotient
        (centralizer ({(z : G)} : Set G) ⧸ Recognition.JankoFour.core (z : G)))
      (X : Sylow 3 (Recognition.JankoFour.LocalGeometry.CubicLift.subgroup cubic)),
      ∃ J : Subgroup (centralizer ({(z : G)} : Set G)),
        Nat.card J=2160 ∧ cubicSylowImage cubic X ≤ J ∧
        J ≤ fullCubicNormalizer cubic X ∧
        J ≤ (normalizer (D.sourceOrbit : Set G)).subgroupOf (centralizer ({(z : G)} : Set G)) ∧
        Disjoint (D.sourceOrbit.subgroupOf (centralizer ({(z : G)} : Set G)) ⊔
          Recognition.JankoFour.core (z : G)) J ∧
        ∀ (P : Subgroup (centralizer ({(z : G)} : Set G))), IsElementaryAbelian 2 P →
          P ≤ Recognition.JankoFour.core (z : G) → Nat.card P=128 →
          (D.sourceOrbit.subgroupOf (centralizer ({(z : G)} : Set G)) ⊓
            Recognition.JankoFour.core (z : G)) ⊓ P = center (centralizer ({(z : G)} : Set G)) →
          J ≤ normalizer (P : Set (centralizer ({(z : G)} : Set G))) →
          ∃ data : Recognition.JankoFour.LocalGeometry.LocalSubgroups.PointData (z : G),
            data.cubic=cubic ∧ ∃ hm : data.M=normalizer (D.sourceOrbit : Set G),
              (∀ x, a (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
                (MulEquiv.subgroupCongr hm (data.toddEquiv x)))=x.right) ∧
              (∀ w : D.sourceOrbit,
                (data.toddEquiv (SemidirectProduct.inl
                  (Multiplicative.ofAdd (E (Additive.ofMul w))))).val=w.val) := by
  intro cubic X
  have ht := D.sourceOrbit_m24_isTypeJ4 h hmany hV hq hnon a E hE z hz hne hquot
  obtain ⟨B,hB,hpre,A,v,t,hAc,_,_,him,_,_,_,_,_,hv,hvo,hvA,hJc,_,_,hJN,hXJ,hJM⟩ :=
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
  refine ⟨J,hJc,hXJ,hJN,hJM,hdis,?_⟩
  intro P hP hPQ hPc hEP hJP
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
