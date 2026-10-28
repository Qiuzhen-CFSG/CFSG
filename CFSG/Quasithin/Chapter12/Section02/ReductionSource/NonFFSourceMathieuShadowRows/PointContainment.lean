module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.PushingUp
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.NearAvoidanceApplication
public import CFSG.Quasithin.Chapter8.Section01.MathieuShadowRows.OrdinaryRank
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourOrdinary
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.Janko

/-!
# Distinguished-point containment and the original M22 cocode exclusion

The original point residual supplies C.2.8 with projective model PSL₃(4).
The field-four pushing-up sieve forces any escaping ordinary component
to contain the entire original module. Its image modulo the component center
has binary rank at least nine. The ordinary sieve therefore gives a J₄
central quotient, whose two-primary covering rigidity contradicts the
original distinguished involution in its center. Thus every distinguished
point centralizer lies in the original normalizer. The earlier full-actor
fixed-span argument then excludes the original M22 cocode row entirely.

Source: Aschbacher--Smith 8.1.1--3 and C.4.8, printed pp.712--714,151.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- Restrict the literal original point map to its embedded perfect residual.
Its full kernel still centralizes the entire original cocode. -/
theorem sourceOrbit_m22_cocode_residual_action
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCocodeRepresentation)
    (x : D.sourceOrbit) (i : Fin 22)
    (hx : (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
      (Additive.ofMul x) = m22WeightTwoVector i) :
    let C := L ⊓ centralizer ({(x : G)} : Set G)
    let B := (solvableResidual C).map C.subtype
    ∃ f : B →* Matrix.PSL3Four.PSL, Function.Surjective f ∧
      f.ker ≤ (centralizer (D.sourceOrbit : Set G)).subgroupOf B := by
  let C := L ⊓ centralizer ({(x : G)} : Set G)
  let R := solvableResidual C
  let B := R.map C.subtype
  obtain ⟨f,hf,_,hk,_⟩ := D.sourceOrbit_m22_cocode_point_residual d x i hx
  let g : R →* Matrix.PSL3Four.PSL := f.comp R.subtype
  have hg : Function.Surjective g := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,range_subtype,map_solvableResidual_eq f hf,solvableResidual_eq_top]
  let e : R ≃* B := R.equivMapOfInjective C.subtype C.subtype_injective
  refine ⟨g.comp e.symm.toMonoidHom,hg.comp e.symm.surjective,?_⟩
  intro b hb
  have hh : (e.symm b : C) ∈ f.ker := hb
  rw [hk] at hh
  have hv : (((e.symm b : R) : C) : G) = (b : G) := by
    exact congrArg B.subtype (e.apply_symm_apply b)
  change (b : G) ∈ centralizer (D.sourceOrbit : Set G)
  rw [←hv]
  exact hh

/-- Source 8.1.1 on the same original M22 cocode vector and normalizer. -/
theorem sourceOrbit_m22_cocode_point_control_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCocodeRepresentation) :
    ∀ x : D.sourceOrbit,
      (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
        (Additive.ofMul x) ∈ m22WeightTwoFamily →
      centralizer ({(x : G)} : Set G) ≤ normalizer (L : Set G) := by
  intro x hx
  obtain ⟨i,hx⟩ := hx
  change m22WeightTwoVector i = _ at hx
  let H := centralizer ({(x : G)} : Set G)
  let A := H ⊓ normalizer (L : Set G)
  let C := L ⊓ H
  let B := (solvableResidual C).map C.subtype
  obtain ⟨hc,hq,⟨e⟩⟩ := D.sourceOrbit_m22_cocode_hypothesisC28_of_many
    h hmany hV hnon d x i hx.symm
  let : IsQuasisimple (B ⧸ pCore 2 B) := hq
  obtain ⟨hn,_,_,_,hspan⟩ := D.sourceOrbit_m22_cocode_point_component
    h.toHypothesis1221 d x i hx.symm
  have hWB : D.sourceOrbit ≤ B := by simpa only [hspan] using hc.module_le
  have hm : D.sourceOrbit = ⁅D.sourceOrbit,B⁆ := by
    simpa only [hspan] using hc.module_commutator
  have hx1 : x ≠ 1 := by
    intro he
    apply m22WeightTwoVector_ne_zero i
    rw [hx,he]
    exact LinearEquiv.map_zero _
  by_contra hout
  have hstrict : A < H := lt_of_le_of_ne inf_le_left
    (fun he => hout (he.symm.le.trans inf_le_right))
  obtain ⟨K,hK,hnK,houtK,hBK,hWK⟩ :=
    field_four_pushingUp_ordinary hc hstrict hn Matrix.PSL3Four.card_F e
  let J := K.map H.subtype
  have hBJ : B ≤ J := by
    intro b hb
    have hBH : B ≤ H := (map_subtype_le _).trans inf_le_right
    exact ⟨⟨b,hBH hb⟩,hBK hb,rfl⟩
  obtain ⟨f,hf,hker⟩ := D.sourceOrbit_m22_cocode_residual_action d x i hx.symm
  have hr := Chapter8.MathieuShadowRows.point_residual_central_quotient_twoRank
    B J D.sourceOrbit hBJ hWB hc.module_nontrivial hm f hf hker
  let eK : K ≃* J := K.equivMapOfInjective H.subtype H.subtype_injective
  let eZ : (K ⧸ center K) ≃* (J ⧸ center J) :=
    QuotientGroup.congr _ _ eK (FixedElementary.map_center eK)
  have hrK : 8 ≤ primeRank 2 (K ⧸ center K) := by
    have hh := Theory.GroupTheory.primeRank_le_of_injective 2 eZ.symm.toMonoidHom eZ.symm.injective
    omega
  obtain ⟨a⟩ := field_four_ordinary_janko_four hc Matrix.PSL3Four.card_F e K hK hrK
  let := hK.2
  have hp : IsPGroup 2 (center K) := by
    rw [IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hc.oddCore_eq_bot K)]
    exact pCore_isPGroup
  have hz := Janko4.TwoPrimary.center_eq_bot_of_quotient_equiv a hp
  have hxH : (x : G) ∈ H := mem_centralizer_singleton_iff.mpr (Commute.refl _).eq
  let xH : H := ⟨x,hxH⟩
  let xK : K := ⟨xH,hWK (show xH ∈ D.sourceOrbit.subgroupOf H from x.property)⟩
  have hxZ : xK ∈ center K := by
    apply mem_center_iff.mpr
    intro k
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp k.val.property
  have hx0 : xK = 1 := mem_bot.mp (show xK ∈ (⊥ : Subgroup K) from hz ▸ hxZ)
  apply hx1
  exact Subtype.ext (congrArg (fun z : K => ((z : H) : G)) hx0)

/-- Source 8.1.3 excludes the original simple M22 cocode row with no
point-containment, escaping-rank or fixed-span premise left over. -/
theorem sourceOrbit_not_m22_cocode_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : Chapter7.NormalizedSource.HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ¬ Nonempty (M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCocodeRepresentation) := by
  rintro ⟨d⟩
  exact D.sourceOrbit_not_m22_cocode_of_point_control h hmany hV hm hnon d
    (D.sourceOrbit_m22_cocode_point_control_of_many h hmany hV hnon d)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
