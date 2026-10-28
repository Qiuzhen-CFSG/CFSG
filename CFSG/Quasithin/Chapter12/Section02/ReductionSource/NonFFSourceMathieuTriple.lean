module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTripleBounds
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuAutomizer
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# Excluding the genuine triple M22 cover on the original chosen orbit

The original component action factors faithfully into the full source-orbit
automizer. Its normality and the native matrix normalizer extend the chosen
triple-cover intertwiner to every ambient actor. The resulting actual action
has two-rank at most five, no near-offenders, and odd-prime displacement at
least eight. The proved odd-normalizer control then discharges E.6.27 and
gives r >= 8. Weak closure gives r <= 5+2, excluding this source branch.

The M22 quotient consequently has a concrete simple code or cocode marking.
The simple M22 and large Mathieu endgame and the ambient J4 isomorphism stay
with the normalized Mathieu assembly; no J4 recognition is asserted here.
Source: Aschbacher--Smith Table 7.2.1,7.4.1 and7.5.2(1), pp.698--700.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTriple
open Sporadic.Mathieu
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
private theorem marking_component_equivariant
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (J : Subgroup A)
    (d : ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M22Source.MarkedTripleModel ρ J)
    (a : J) (v : W) : d.equivalence (ρ a v) =
      M22TripleCover.binaryRepresentation (d.componentEquiv a) (d.equivalence v) := by
  have he := LinearMap.congr_fun (d.equivalence.isIntertwining' (a : A)) v
  change d.equivalence (ρ a v) =
    M22TripleCover.Ambient.binaryAction (d.embedding a) (d.equivalence v) at he
  rw [d.on_component a] at he
  exact he

private theorem change_coordinates
    {E W U : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup U] [Module (ZMod 2) U]
    (c : E ≃ₗ[ZMod 2] W) (e : E ≃ₗ[ZMod 2] U)
    (f : E →ₗ[ZMod 2] E) (g : W →ₗ[ZMod 2] W) (a : U →ₗ[ZMod 2] U)
    (hc : ∀ v, c (f v) = g (c v)) (he : ∀ v, e (f v) = a (e v)) (v : U) :
    (e.symm.trans c) (a v) = g ((e.symm.trans c) v) := by
  obtain ⟨w,rfl⟩ := e.surjective v
  change c (e.symm (a (e w))) = g (c (e.symm (e w)))
  rw [←he,e.symm_apply_apply,e.symm_apply_apply,hc]

private theorem marking_of_quotient
    {A B W : Type*} [Group A] [Finite A] [Group B]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (hρ : Function.Injective ρ)
    (q : B →* M22TripleCover) (hq : Function.Surjective q)
    (k : B →* A) [k.range.Normal] (c : M22TripleCover.BinarySpace ≃ₗ[ZMod 2] W)
    (hc : ∀ b v, c (M22TripleCover.binaryRepresentation (q b) v) = ρ (k b) (c v)) :
    ∃ j : A →* actionGroup, Function.Injective j ∧
      Nonempty (ρ.Equiv (M22TripleCover.Ambient.binaryAction.comp j)) := by
  obtain ⟨f,hf,he,hfq⟩ := faithful_action_factor M22TripleCover.binaryRepresentation ρ
    M22TripleCover.binaryRepresentation_faithful hρ q hq k c hc
  have hfr : f.range = k.range := by
    have hcomp : f.comp q = k := MonoidHom.ext hfq
    rw [←hcomp,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hq,←MonoidHom.range_eq_map]
  let : f.range.Normal := hfr.symm ▸ inferInstance
  let e : f.range ≃* M22TripleCover := (f.ofInjective hf).symm
  let E : Representation.Equiv (ρ.comp f.range.subtype) (M22TripleCover.representationOfEquiv e) :=
    Representation.Equiv.mk c.symm (by
      intro a
      apply LinearMap.ext
      intro v
      obtain ⟨b,rfl⟩ := (f.ofInjective hf).surjective a
      obtain ⟨w,rfl⟩ := c.surjective v
      change c.symm (ρ (f b) (c w)) =
        M22TripleCover.binaryRepresentation ((f.ofInjective hf).symm ((f.ofInjective hf) b))
          (c.symm (c w))
      rw [(f.ofInjective hf).symm_apply_apply,←he,c.symm_apply_apply,c.symm_apply_apply])
  let j := M22TripleCover.Ambient.markedTripleAmbientHom ρ f.range e E
  exact ⟨j,M22TripleCover.Ambient.markedTripleAmbientHom_injective ρ f.range e E hρ,
    ⟨Representation.Equiv.mk E.toLinearEquiv (fun a => LinearMap.ext
      (M22TripleCover.Ambient.markedTripleAmbientHom_intertwining ρ f.range e E a))⟩⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTriple

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The original component marking extends to the full original automizer,
through the literal triple-cover matrix normalizer. -/
theorem sourceOrbit_triple_automizer_marking
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedTripleModel D.orbitRepresentation D.orbitComponent) :
    ∃ j : Automizer D.sourceOrbit →* actionGroup, Function.Injective j ∧
      Nonempty ((automizerRepresentation D.sourceOrbit).Equiv
        (M22TripleCover.Ambient.binaryAction.comp j)) := by
  let N := normalizer (D.sourceOrbit : Set G)
  let qN := D.sourceOrbit.normalizerMonoidHom.rangeRestrict
  let k : L →* Automizer D.sourceOrbit := qN.comp (inclusion D.sourceOrbit_component_normalizes)
  let q : L →* M22TripleCover := d.componentEquiv.toMonoidHom.comp D.orbitComponentHom
  have hq : Function.Surjective q := d.componentEquiv.surjective.comp D.orbitComponentHom_surjective
  have hk : k.range = (L.subgroupOf N).map qN := by
    ext a
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨inclusion D.sourceOrbit_component_normalizes l,l.property,rfl⟩
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,hl⟩,rfl⟩
  let : (L.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer (D.sourceOrbit_normalizer_le h)
  let : k.range.Normal := hk ▸ Normal.map inferInstance qN
    D.sourceOrbit.normalizerMonoidHom.rangeRestrict_surjective
  have hc (l : L) (w : D.orbitSpace) :
      D.sourceOrbitCoordinates (D.orbitRepresentation (D.orbitComponentHom l) w) =
        automizerRepresentation D.sourceOrbit (k l) (D.sourceOrbitCoordinates w) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (D.sourceOrbitCoordinates_apply
      (D.orbitRepresentation (D.orbitComponentHom l) w)).trans
        (congrArg (fun x : G => (l : G) * x * (l : G)⁻¹)
          (D.sourceOrbitCoordinates_apply w).symm)
  have hd (l : L) (v : D.orbitSpace) :
      d.equivalence (D.orbitRepresentation (D.orbitComponentHom l) v) =
        M22TripleCover.binaryRepresentation (q l) (d.equivalence v) :=
    MathieuTriple.marking_component_equivariant _ _ d (D.orbitComponentHom l) v
  exact MathieuTriple.marking_of_quotient
    (automizerRepresentation D.sourceOrbit) (automizerRepresentation_injective _)
    q hq k (d.equivalence.toLinearEquiv.symm.trans D.sourceOrbitCoordinates)
    (fun l v => MathieuTriple.change_coordinates D.sourceOrbitCoordinates d.equivalence.toLinearEquiv
      _ _ _ (hc l) (hd l) v)

private theorem triple_action_bounds
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedTripleModel D.orbitRepresentation D.orbitComponent) :
    primeRank 2 (Automizer D.sourceOrbit) ≤ 5 ∧
      (∀ A : Subgroup (Automizer D.sourceOrbit), IsElementaryTwo A →
        rank A+1 < fixedCodim (automizerRepresentation D.sourceOrbit) A) ∧
      (∀ (p : ℕ), p.Prime → Odd p → ∀ a : Automizer D.sourceOrbit,
        orderOf a = p → 8 ≤ fixedCodim (automizerRepresentation D.sourceOrbit) (zpowers a)) := by
  obtain ⟨j,hj,⟨E⟩⟩ := D.sourceOrbit_triple_automizer_marking h d
  refine ⟨(_root_.primeRank_le_of_injective 2 j hj).trans
    M22TripleCover.NoFF.ambient_twoRank_le_five,?_,?_⟩
  · intro A hA
    let := hA.2
    have hB : IsElementaryTwo (A.map j) := ⟨fun hb => hA.1 ((Subgroup.map_eq_bot_iff_of_injective A hj).mp hb),
      IsElementaryAbelian.map _⟩
    have he := fixedCodim_map_equivariant (automizerRepresentation D.sourceOrbit)
      M22TripleCover.Ambient.binaryAction j E.toLinearEquiv
      (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v) A
    have hb := MathieuTriple.ambient_fixedCodim_gap (A.map j) hB
    rw [rank_map_injective,←he] at hb
    · exact hb
    · exact hj
  · intro p hp ho a ha
    have he := fixedCodim_map_equivariant (automizerRepresentation D.sourceOrbit)
      M22TripleCover.Ambient.binaryAction j E.toLinearEquiv
      (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v) (zpowers a)
    rw [MonoidHom.map_zpowers] at he
    rw [he]
    exact MathieuTriple.ambient_odd_fixedCodim hp ho (j a)
      ((orderOf_injective j hj a).trans ha)

open ChapterE.Section06 ChapterE.Section06.FixedPointBounds
/-- The near-offender gap and odd displacement discharge E.6.27 for every
nonzero original-orbit subspace of corank less than eight. -/
theorem sourceOrbit_triple_small_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedTripleModel D.orbitRepresentation D.orbitComponent)
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit)
    (hsmall : subgroupCorank D.sourceOrbit U < 8) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  have h61 := D.sourceOrbit_hypothesisE61_of_many h hmany hnon hV
  have hp := D.sourceOrbit_mathieu_initial_parameters h hmany hV hm hnon
  have hsr : globalS D.sourceOrbit ≤ globalR D.sourceOrbit := by rw [hp.2.1]; exact hp.1
  obtain ⟨_,hgap,hodd⟩ := D.triple_action_bounds h.toHypothesis1221 d
  apply source_proposition_E_6_27 h61 hU hUW (j := 1) (by decide) ?_ ?_ ?_
    (D.sourceOrbit_mathieu_odd_normalizer_le h hmany hV hm hnon)
  · exact lt_of_lt_of_le (lt_trans (by decide : (1 : ℕ∞) < 2) hp.2.2) hsr
  · apply induced_nPrime_le_one_of_odd_fixedCodim D.sourceOrbit _ U
      (h61.localCentralizer_le_normalizer hU hUW) hUW inf_le_right (b := 8) (c := 1)
    · intro p hp ho a ha
      simpa using hodd p hp ho a ha
    · simpa using hsmall
  · exact le_inf (ChapterB.thompsonJ_le _ _ |>.trans inf_le_left)
      (thompson_centralizes_of_fixedCodim_gap D.sourceOrbit _
        (h61.normal_in_localCentralizer hU hUW).1
        (h61.localCentralizer_le_normalizer hU hUW) hgap)

/-- Source 7.4.1 supplies r >= 8 for the actual triple-cover branch. -/
theorem sourceOrbit_triple_globalR_ge_eight
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedTripleModel D.orbitRepresentation D.orbitComponent) :
    8 ≤ globalR D.sourceOrbit := by
  apply D.sourceOrbit_globalR_lower_of_local_ranks h hmany hnon hV
    ((by decide : 8 ≤ 10).trans (D.sourceOrbit_mathieu_rank_ge_ten hV hm))
  intro U hUW hU hescape
  have hcor : 8 ≤ subgroupCorank D.sourceOrbit U := by
    by_contra hlt
    exact hescape (D.sourceOrbit_triple_small_centralizer h hmany hV hm hnon d hU hUW (by omega))
  have hdim := offender_corank_add (B := (⊥ : Subgroup G)) bot_le hUW
  have heq : rank D.sourceOrbit = subgroupCorank D.sourceOrbit U + rank U := by
    simpa only [subgroupCorank,relIndex_bot_left,rank] using hdim
  omega

/-- The literal triple-cover marking is impossible by r >= 8 > 5+2 >= r. -/
theorem sourceOrbit_not_triple_marked_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ¬ Nonempty (M22Source.MarkedTripleModel D.orbitRepresentation D.orbitComponent) := by
  rintro ⟨d⟩
  have hlo := D.sourceOrbit_triple_globalR_ge_eight h hmany hV hm hnon d
  have hhi := Chapter7.fwci_upper_bound D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon)
    (D.triple_action_bounds h.toHypothesis1221 d).1
    (D.sourceOrbit_mathieu_globalW_le_two h hmany hV hm hnon)
  norm_num at hhi
  exact (by decide : ¬ (8 : ℕ∞) ≤ 7) (hlo.trans hhi)

/-- The original M22 quotient is now concretely simple code or cocode;
there is no remaining triple-cover alternative or local-action callback. -/
theorem sourceOrbit_m22_simple_marking_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M22))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    Nonempty (M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      MathieuCode.m22OuterCodeRepresentation) ∨
    Nonempty (M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      MathieuCode.m22OuterCocodeRepresentation) := by
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inr (Or.inl hq)
  rcases MathieuMarkings.m22_marking D.orbitRepresentation D.orbitComponent
    (D.sourceOrbit_chapterK_of_many h hmany hnon hV) hq with hc | hd | ht
  · exact Or.inl hc
  · exact Or.inr hd
  · exact (D.sourceOrbit_not_triple_marked_of_many h hmany hV hm hnon ht).elim

/-- The actual triple cover, rather than a family label, is excluded on the
original orbit component in the M22 quotient branch. -/
theorem sourceOrbit_not_tripleM22_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M22))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ¬ Nonempty (D.orbitComponent ≃* M22TripleCover) := by
  rintro ⟨e⟩
  rcases D.sourceOrbit_m22_simple_marking_of_many h hmany hV hq hnon with hc | hc
  all_goals
    let d := Classical.choice hc
    have he := Nat.card_congr (e.symm.trans d.componentEquiv).toEquiv
    norm_num only [M22TripleCover.card,m22_order] at he
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
