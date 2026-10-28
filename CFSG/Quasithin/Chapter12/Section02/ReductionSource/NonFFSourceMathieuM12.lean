module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuM12Bounds
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuAutomizer
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# Original-orbit M12 parameters

The original component marking extends to the whole ambient automizer,
including outer actors, and identifies its actual solvable residual. The
native odd-prime displacement and strict near-offender gap discharge the
local action premises of E.6.27. The existing odd-normalizer control gives
r >= 6; the weak-closure inequality then forces r = 6, w = 2 and m2 = 4.

The terminal fixed-space contradiction is separate; these numerical
parameters alone do not prove the M12 exclusion or recognize J4.
Source: Aschbacher--Smith 7.2.1,7.4.1,7.5.4 and E.6.27, pp.698--700,257.
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuM12
open ChapterH.Section10To12 ChapterH.Section10To12.M12Calculations Sporadic.Mathieu
private theorem marking_component_equivariant
    {A W : Type*} [Group A] [Finite A]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (J : Subgroup A)
    (d : MathieuMarkings.M12Marking ρ J) (a : J) (v : W) :
    d.equivalence (ρ a v) = m12HeartRepresentation (d.component a) (d.equivalence v) := by
  have he := LinearMap.congr_fun (d.equivalence.isIntertwining' (a : A)) v
  change d.equivalence (ρ a v) =
    Ambient.automorphismRepresentation (d.embedding a) (d.equivalence v) at he
  rw [d.on_component] at he
  have hi := congrArg (fun τ => τ (d.component a)) Ambient.automorphismRepresentation_inner
  exact he.trans (congrArg (fun f => f (d.equivalence v)) hi)

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

private theorem input_of_heart_quotient
    {A B W : Type*} [Group A] [Finite A] [Group B]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (hρ : Function.Injective ρ)
    (q : B →* M12) (hq : Function.Surjective q)
    (k : B →* A) [k.range.Normal] (c : M12Heart ≃ₗ[ZMod 2] W)
    (hc : ∀ b v, c (m12HeartRepresentation (q b) v) = ρ (k b) (c v)) :
    Nonempty (M12ModuleInput ρ) := by
  obtain ⟨f,hf,he,hfq⟩ := faithful_action_factor m12HeartRepresentation ρ
    Ambient.heartRepresentation_faithful hρ q hq k c hc
  have hfr : f.range = k.range := by
    have hcomp : f.comp q = k := MonoidHom.ext hfq
    rw [←hcomp,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hq,←MonoidHom.range_eq_map]
  let : f.range.Normal := hfr.symm ▸ inferInstance
  let e : f.range ≃* M12 := (f.ofInjective hf).symm
  let : Group.IsPerfect f.range := Group.IsPerfect.ofSurjective f.rangeRestrict_surjective
  apply input_of_normal_heart ρ hρ f.range e c.symm
  intro a v
  obtain ⟨b,rfl⟩ := (f.ofInjective hf).surjective a
  obtain ⟨w,rfl⟩ := c.surjective v
  dsimp only [e]
  rw [(f.ofInjective hf).symm_apply_apply]
  change c.symm (ρ (f b) (c w)) = m12HeartRepresentation b (c.symm (c w))
  rw [←he,c.symm_apply_apply,c.symm_apply_apply]

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuM12

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu
open ChapterH.Section10To12 ChapterH.Section10To12.M12Calculations
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The M12 heart marking on the full original automizer, with its actual solvable residual. -/
theorem sourceOrbit_m12_automizer_marking
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M12)) :
    Nonempty (M12ModuleInput (automizerRepresentation D.sourceOrbit)) := by
  obtain ⟨d⟩ := MathieuMarkings.m12_marking D.orbitRepresentation D.orbitComponent hs hq
  let N := normalizer (D.sourceOrbit : Set G)
  let qN := D.sourceOrbit.normalizerMonoidHom.rangeRestrict
  let k : L →* Automizer D.sourceOrbit := qN.comp (inclusion D.sourceOrbit_component_normalizes)
  let q : L →* M12 := d.component.toMonoidHom.comp D.orbitComponentHom
  have hq' : Function.Surjective q := d.component.surjective.comp D.orbitComponentHom_surjective
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
        m12HeartRepresentation (q l) (d.equivalence v) := by
    exact MathieuM12.marking_component_equivariant _ _ d (D.orbitComponentHom l) v
  exact MathieuM12.input_of_heart_quotient
    (automizerRepresentation D.sourceOrbit) (automizerRepresentation_injective _)
    q hq' k (d.equivalence.toLinearEquiv.symm.trans D.sourceOrbitCoordinates)
    (fun l v => MathieuM12.change_coordinates D.sourceOrbitCoordinates d.equivalence.toLinearEquiv
      _ _ _ (hc l) (hd l) v)

open ChapterE.Section06 ChapterE.Section06.FixedPointBounds
/-- The two H.16 displacement estimates discharge both local-action premises
of E.6.27 for a nonzero heart subspace of corank less than six. -/
theorem sourceOrbit_m12_small_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hc : M12ModuleInput (automizerRepresentation D.sourceOrbit))
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit)
    (hsmall : subgroupCorank D.sourceOrbit U < 6) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  have h61 := D.sourceOrbit_hypothesisE61_of_many h hmany hnon hV
  have hp := D.sourceOrbit_mathieu_initial_parameters h hmany hV hm hnon
  have hsr : globalS D.sourceOrbit ≤ globalR D.sourceOrbit := by rw [hp.2.1]; exact hp.1
  apply source_proposition_E_6_27 h61 hU hUW (j := 1) (by decide) ?_ ?_ ?_
    (D.sourceOrbit_mathieu_odd_normalizer_le h hmany hV hm hnon)
  · exact lt_of_lt_of_le (lt_trans (by decide : (1 : ℕ∞) < 2) hp.2.2) hsr
  · apply induced_nPrime_le_one_of_odd_fixedCodim D.sourceOrbit _ U
      (h61.localCentralizer_le_normalizer hU hUW) hUW inf_le_right (b := 6) (c := 1)
    · intro p hp ho a ha
      simpa using MathieuM12.odd_fixedCodim_ge_six _ hc hp ho a ha
    · simpa using hsmall
  · exact le_inf (ChapterB.thompsonJ_le _ _ |>.trans inf_le_left)
      (thompson_centralizes_of_fixedCodim_gap D.sourceOrbit _
        (h61.normal_in_localCentralizer hU hUW).1
        (h61.localCentralizer_le_normalizer hU hUW)
        (MathieuM12.fixedCodim_gap _ hc))

/-- Source 7.4.1 for the original M12 heart automizer, with every local
rank, normalizer and representation premise discharged. -/
theorem sourceOrbit_m12_globalR_ge_six
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M12))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    6 ≤ globalR D.sourceOrbit := by
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inl hq
  obtain ⟨hc⟩ := D.sourceOrbit_m12_automizer_marking h.toHypothesis1221
    (D.sourceOrbit_chapterK_of_many h hmany hnon hV) hq
  apply D.sourceOrbit_globalR_lower_of_local_ranks h hmany hnon hV
    ((by decide : 6 ≤ 10).trans (D.sourceOrbit_mathieu_rank_ge_ten hV hm))
  intro U hUW hU hescape
  have hcor : 6 ≤ subgroupCorank D.sourceOrbit U := by
    by_contra hlt
    exact hescape (D.sourceOrbit_m12_small_centralizer h hmany hV hm hnon hc hU hUW
      (by omega))
  have hdim := offender_corank_add (B := (⊥ : Subgroup G)) bot_le hUW
  have heq : rank D.sourceOrbit = subgroupCorank D.sourceOrbit U + rank U := by
    simpa only [subgroupCorank,relIndex_bot_left,rank] using hdim
  omega

/-- Exact source M12 numerical row, with all original-orbit inputs discharged. -/
theorem sourceOrbit_m12_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M12))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    globalW D.sourceOrbit T = 2 ∧ primeRank 2 (Automizer D.sourceOrbit) = 4 ∧
      globalR D.sourceOrbit = 6 ∧ localM D.sourceOrbit = 4 := by
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inl hq
  obtain ⟨hc⟩ := D.sourceOrbit_m12_automizer_marking h.toHypothesis1221
    (D.sourceOrbit_chapterK_of_many h hmany hnon hV) hq
  have hq4 := (ambientExtension _ hc).primeRank_le_four M12AutomorphismRank.twoRank_le_four
  obtain ⟨hw,hq',hr,_⟩ := Chapter7.mathieu_forced_parameters D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon) hq4
    (D.sourceOrbit_mathieu_globalW_le_two h hmany hV hm hnon)
    (D.sourceOrbit_m12_globalR_ge_six h hmany hV hq hnon)
  exact ⟨hw,hq',hr,MathieuM12.moduleM_eq_four _ hc⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
