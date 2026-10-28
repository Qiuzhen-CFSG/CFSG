module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeCartanCubic
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CartanOrbitTorus
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeFixedTorus
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Pair

/-!
# Field four in the original M22-code Cartan branch

The original overlap centralizes the nonzero Sylow-fixed vector in the
original orbit. Transport through the actual full automizer marking makes
this a marked M22 hexad vector. The split torus constructed on the faithful
whole-span image embeds in its stabilizer. Its order divides 5760; the
absence of elements of order fifteen in M22 then forces field order four.
This specializes the field reduction of 3.1.9(6) directly to the actual
M22-code model, without an extra Cartan-centralization premise.

The field-four conclusion discharges the three-divisibility input to the
existing cubic construction. The final theorem constructs the original
essential action and same minimum sharp actor, with either its small natural
alternative or its field-four Cartan and three chief factors on the original
code and dual. All original covering maps and their full kernels remain;
no representative is asserted to have order three upstairs in H.

The two-factor upper count, symmetric-five exclusions, inside-core exclusion
and final same-orbit M24-cocode selection remain subsequent source steps.
Source: Aschbacher--Smith, 3.1.9(6), printed p.578, and 8.2.2(1), p.715,
refs/quasithin.pdf. The private import reuses the proved original H-star
normalization without changing its public boundary.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode Sporadic.Mathieu
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterD NoncentralChiefRefinement
open Chapter8.MathieuShadowRows
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem original_m22_code_sylow_fixed
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) :
    ∃ S : Sylow 2 M22,
      (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv) (Additive.ofMul z) ∈
        fixedSpace m22CodeRepresentation S := by
  let N := normalizer (L : Set G)
  let LN := L.subgroupOf N
  let : LN.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let ST := T.subtype D.sylow_normalizes_component
  obtain ⟨P₀,hP₀⟩ := ST.exists_subgroupOf_eq_of_normal LN
  let e : LN ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let P := P₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPT (l : L) (hl : l ∈ (P : Subgroup L)) : (l : G) ∈ (T : Subgroup G) := by
    obtain ⟨x,hx,rfl⟩ := hl
    rw [hP₀] at hx
    exact hx
  let q := d.componentEquiv.toMonoidHom.comp D.orbitComponentHom
  have hq : Function.Surjective q := d.componentEquiv.surjective.comp
    D.orbitComponentHom_surjective
  refine ⟨P.mapSurjective hq,?_⟩
  rintro ⟨_,l,hl,rfl⟩
  let E := D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv
  have he := D.sourceOrbit_m22_component_coordinates m22CodeRepresentation
    m22OuterCodeRepresentation (by
      apply MonoidHom.ext
      intro g
      apply LinearMap.ext
      intro v
      exact m22OuterCodeRepresentation_restrict g v) d l (Additive.ofMul z)
  change m22CodeRepresentation (d.componentEquiv (D.orbitComponentHom l))
    (E (Additive.ofMul z)) = E (Additive.ofMul z)
  rw [←he]
  congr 1
  apply Additive.toMul.injective
  apply Subtype.ext
  change (l : G) * (z : G) * (l : G)⁻¹ = (z : G)
  rw [mul_inv_eq_iff_eq_mul]
  exact mem_centralizer_iff.mp hz l (hPT l hl)

private theorem original_m22_code_overlap_torus_field_four
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (hlarge : 4 ≤ Nat.card F)
    (t : Fˣ →* Automizer D.sourceOrbit) (ht : Function.Injective t)
    (hlift : ∀ u, ∃ b : H, ∃ hn : (b : G) ∈ normalizer (D.sourceOrbit : Set G),
      D.sourceOrbit.normalizerMonoidHom.rangeRestrict ⟨(b : G),hn⟩ = t u) :
    Nat.card F = 4 := by
  obtain ⟨f,hf,hE,_⟩ := D.sourceOrbit_m22_code_full_automizer h.toHypothesis1221 d
  let E := D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv
  have hZ : D.sourceOrbit ⊓ centralizer (T : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot_of_pGroups (T : Subgroup G) D.sourceOrbit T.isPGroup'
      (IsElementaryAbelian.isPGroup 2 D.sourceOrbit)
      D.sourceOrbit_weakClosure_setup.normalizes D.sourceOrbit_weakClosure_setup.nontrivial
  obtain ⟨⟨z,hz⟩,hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
  have hz1 : z ≠ 1 := fun he => hz1' (Subtype.ext he)
  let z₀ : Additive D.sourceOrbit := Additive.ofMul ⟨z,hz.1⟩
  have hz0 : E z₀ ≠ 0 := by
    intro he
    have hz' := E.injective (he.trans E.map_zero.symm)
    exact hz1 (congrArg (fun w : Additive D.sourceOrbit => (w.toMul : G)) hz')
  obtain ⟨S,hS⟩ := D.original_m22_code_sylow_fixed d ⟨z,hz.1⟩ hz.2
  have hzOmega : z ∈ omegaOneCenterAmbient (T : Subgroup G) :=
    (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨D.sourceOrbit_weakClosure_setup.le_sylow hz.1,
        elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz.1,hz.2⟩
  apply NormalizedShadowRows.code_fixed_split_torus_field_four F hlarge
    (f.comp t) (hf.comp ht) S (E z₀) hz0 hS
  intro u
  change m22OuterCodeRepresentation (f (t u)) (E z₀) = E z₀
  rw [←hE]
  obtain ⟨b,hn,hb⟩ := hlift u
  rw [←hb]
  congr 1
  apply Additive.toMul.injective
  apply Subtype.ext
  change (b : G) * z * (b : G)⁻¹ = z
  rw [mul_inv_eq_iff_eq_mul]
  exact ((D.sourceOrbit_hstar_centralizes_omega h.toHypothesis1221 hnon hH)
    b.property z hzOmega).symm

set_option backward.isDefEq.respectTransparency false in
/-- The original M22-code Cartan has field four, with no additional
three-group, fixed-vector, or model premise. -/
theorem sourceOrbit_m22_code_cartan_field_four
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2)
    [hU : IsElementaryAbelian 2 ((conjugateSpan H D.sourceOrbit).subgroupOf H)]
    (a : Chapter3.EssentialSeedAction H D.sourceOrbit (T.subtype hH.1.1.2)
      (hcore.trans (ChapterD.UniqueFactor.twoCore_le H)))
    (A : Subgroup H) (ha : EssentialChiefActor a A)
    (c : SeedCartan (M := normalizer (L : Set G)) a.projection a.imageRepresentation a.vector) :
    Nat.card c.field.Carrier = 4 := by
  have hN := D.m24_hstar_normalizes h hmany hV hnon hH
  have hc := D.sourceOrbit_m22_code_cartan_span_cover h hmany hV hnon d hH hcore a A ha c
  obtain ⟨t,ht,hlift⟩ := c.exists_orbit_torus (D := a.Actor) (W := a.socle.toSubmodule)
    (H := H) (V := D.sourceOrbit) (q := a.projection)
    (ρ := a.imageRepresentation) (v := a.vector) (hU := hU)
    (hcore.trans (ChapterD.UniqueFactor.twoCore_le H)) a.vector_centralizer_fixed hN hc
  apply D.original_m22_code_overlap_torus_field_four h hnon d hH
    c.field.Carrier c.large t ht
  intro u
  exact ⟨((hlift u).choose : H), (hlift u).choose_spec.2⟩

set_option backward.isDefEq.respectTransparency false in
/-- The original Cartan is cubic, and its constructed action on the same
original code and dual has three noncentral chief factors. -/
theorem sourceOrbit_m22_code_cartan_field_four_chiefs
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2)
    [hU : IsElementaryAbelian 2 ((conjugateSpan H D.sourceOrbit).subgroupOf H)]
    (a : Chapter3.EssentialSeedAction H D.sourceOrbit (T.subtype hH.1.1.2)
      (hcore.trans (ChapterD.UniqueFactor.twoCore_le H)))
    (A : Subgroup H) (ha : EssentialChiefActor a A)
    (c : SeedCartan (M := normalizer (L : Set G)) a.projection a.imageRepresentation a.vector) :
    Nat.card c.field.Carrier = 4 ∧ Nat.card c.field.Carrierˣ = 3 ∧
      CubicOrbitChiefs (V := D.sourceOrbit) c.originalPreimage a.projection := by
  have hfour := D.sourceOrbit_m22_code_cartan_field_four h hmany hV hnon d hH hcore a A ha c
  have hcard : Nat.card c.field.Carrierˣ = 3 := by rw [Nat.card_units,hfour]
  exact ⟨hfour,hcard,D.sourceOrbit_m22_code_cartan_constructed_cubic_chiefs
    h hmany hV hnon d hH hcore a A ha c (by rw [hcard])⟩

set_option backward.isDefEq.respectTransparency false in
/-- The original nonsolvable inside-core branch constructs either its small
natural action or a field-four Cartan with actual cubic actions and three
chief factors on the unchanged original code and dual. No additional Cartan
centralization, three-group, or model premise remains. -/
theorem sourceOrbit_m22_code_inside_core_nonsolvable_cubic_alternatives
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) (hns : ¬ Group.IsSolvable H) :
    let U := (conjugateSpan H D.sourceOrbit).subgroupOf H
    ∃ hU : IsElementaryAbelian 2 U,
      let := hU
      ∃ a : Chapter3.EssentialSeedAction H D.sourceOrbit (T.subtype hH.1.1.2)
          (hcore.trans (ChapterD.UniqueFactor.twoCore_le H)),
        ∃ A ∈ elementaryAbelianMaxSubgroups ((T.subtype hH.1.1.2) : Subgroup H),
          ¬ A ≤ pCore 2 H ∧ IsQuadratic (normalRepresentation U) A ∧
          (∀ B ∈ elementaryAbelianMaxSubgroups ((T.subtype hH.1.1.2) : Subgroup H),
            ¬ B ≤ pCore 2 H → (pCore 2 H).relIndex A ≤ (pCore 2 H).relIndex B) ∧
          EssentialChiefActor a A ∧
          FieldFourCubicAlternatives (M := normalizer (L : Set G))
            (V := D.sourceOrbit) a.projection a.imageRepresentation a.vector := by
  obtain ⟨hU,a,A,hA,hAR,hquad,hmin,ha,hc⟩ :=
    D.sourceOrbit_m22_code_inside_core_nonsolvable_cartan h hmany hV hnon d hH hcore hns
  let := hU
  refine ⟨hU,a,A,hA,hAR,hquad,hmin,ha,?_⟩
  rcases hc with hs | ⟨c,_⟩
  · exact Or.inl hs
  · have hf := D.sourceOrbit_m22_code_cartan_field_four_chiefs
      h hmany hV hnon d hH hcore a A ha c
    exact Or.inr ⟨c,IsPGroup.of_card (n := 1) hf.2.1,hf.1,hf.2.2⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
