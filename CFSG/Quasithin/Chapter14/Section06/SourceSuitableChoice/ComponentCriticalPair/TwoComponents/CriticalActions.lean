module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.Endpoints
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.EndpointKernels
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator
public import Theory.ElementaryAbelian.BinaryQuotientRank

/-!
# Literal denominators and quadratic action at the terminal endpoint

F.9's action-kernel equality identifies each commutator denominator with
the intersection of the corresponding module and opposite two-core.
The same critical conjugator is used for both equations. Mutual
commutator containment and abelianness make the actual quotient actor
quadratic; no rank comparison or model classification is assumed.

The two source applications preserve every hypothesis of the original
terminal setup with H=Mc and U=conjugateSpanBy(localModule T M) Mc.
Criticality makes the first denominator positive, and the actor order is
the exact index of its opposite-core intersection. Rank comparison and
placement of the critical point remain separate source arguments.
Source: Aschbacher--Smith F.9.13 and 14.6.24(3), pp.322,1039--1041.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
open Chapter13.Section08.SourceCompletion
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
variable {G : Type*} [Group G] [Finite G] {D : Setup G} (h : D.Hypothesis)

/-- Both literal denominators are the actual opposite-core intersections. -/
theorem CriticalEndpoint.denominators (i : h.CriticalEndpoint) (hb : 3 ≤ h.b) :
    commutatorPreimage D.UH (i.conjugate D.UH) (i.conjugate D.V₁) =
      D.UH ⊓ i.conjugate D.QH ∧
    commutatorPreimage (i.conjugate D.UH) D.UH D.V₁ =
      i.conjugate D.UH ⊓ D.QH := by
  have huv : D.UH ≤ D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  have hback : D.UH.map (MulAut.conj i.representative⁻¹).toMonoidHom ≤ D.H := by
    have hm := map_mono (f := (MulAut.conj i.representative⁻¹).toMonoidHom)
      (huv.trans (i.reverse_le hb))
    rwa [conjugate_inverse_cancel] at hm
  constructor
  · have he := congrArg (fun A : Subgroup G => A.map (MulAut.conj i.representative).toMonoidHom)
      (f9_commutatorPreimage_eq D h
        (D.UH.map (MulAut.conj i.representative⁻¹).toMonoidHom) hback)
    have hn := hback.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    rw [map_commutatorPreimage_equiv _ _ _ _ hn,
      map_inf _ _ _ (MulAut.conj i.representative).injective] at he
    have hc : (D.UH.map (MulAut.conj i.representative⁻¹).toMonoidHom).map
        (MulAut.conj i.representative).toMonoidHom = D.UH := by
      simpa only [inv_inv] using conjugate_inverse_cancel i.representative⁻¹ D.UH
    rwa [hc] at he
  · exact f9_commutatorPreimage_eq D h (i.conjugate D.UH)
      ((map_mono huv).trans (i.large_le hb))
end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis



namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} (h : D.Hypothesis)
    {X E : Type*} [Group X] [AddCommGroup E] [Module (ZMod 2) E]
/-- The same critical conjugate acts quadratically on the marked section. -/
theorem CriticalEndpoint.quadratic
    (i : h.CriticalEndpoint) (hb : 3 ≤ h.b) (hUV : D.UH = D.VH)
    (hab : IsMulCommutative D.UH)
    (σ : Representation (ZMod 2) X E) (π : D.H →* X)
    (c : Representation.BinaryConjugationSection D.H D.UH D.V₁ (σ.comp π)) :
    Representation.BinaryOffender.IsQuadratic σ (((i.conjugate D.UH).subgroupOf D.H).map π) := by
  have hAU : ⁅i.conjugate D.UH,D.UH⁆ ≤ i.conjugate D.UH := by
    rw [commutator_comm,hUV]
    exact (i.commutator hb).trans inf_le_right
  have hz : ⁅i.conjugate D.UH,i.conjugate D.UH⁆ = ⊥ := by
    change ⁅D.UH.map _,D.UH.map _⁆ = ⊥
    rw [← map_commutator,commutator_self_eq_bot_iff.mpr hab,Subgroup.map_bot]
  apply Representation.BinaryConjugationSection.isQuadratic_of_triple_commutator_le
    D.H D.UH D.V₁ (i.conjugate D.UH) σ π c
  exact (commutator_mono le_rfl hAU).trans (hz.le.trans bot_le)
end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis

namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {D : Setup G} (h : D.Hypothesis)

/-- Criticality itself makes the original denominator proper. This does
not require any assertion about transvections on the quotient module. -/
theorem CriticalEndpoint.denominator_positive
    (i : h.CriticalEndpoint) (hb : 3 ≤ h.b) (hplus : D.Vplus = D.V) :
    0 < Nat.log 2 ((D.UH ⊓ i.conjugate D.QH).relIndex D.UH) := by
  have hVU : D.V ≤ D.UH := by
    change D.V ≤ conjugateSpanBy D.Vplus D.H
    rw [hplus]
    exact le_conjugateSpanBy _ _
  have hn : D.UH ≤ normalizer (i.conjugate D.V₁ : Set G) := by
    have hh := map_mono (f := (MulAut.conj i.representative).toMonoidHom)
      (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    rw [map_equiv_normalizer_eq] at hh
    exact (conjugateSpanBy_mono h.plus_le le_rfl).trans ((i.reverse_le hb).trans hh)
  have hne : (D.UH ⊓ i.conjugate D.QH).relIndex D.UH ≠ 1 := by
    intro he
    have hd := le_antisymm inf_le_left (relIndex_eq_one.mp he)
    have hc := commutator_commutatorPreimage_le D.UH (i.conjugate D.UH)
      (i.conjugate D.V₁) hn
    rw [(i.denominators h hb).1, hd, commutator_comm] at hc
    exact i.noncentral ((commutator_mono le_rfl hVU).trans hc)
  have hp : (D.UH ⊓ i.conjugate D.QH).relIndex D.UH ≠ 0 := index_ne_zero_of_finite
  exact Nat.log_pos (by decide) (by omega)

/-- The star-actor order is the index of the literal opposite-core kernel. -/
theorem CriticalEndpoint.actor_card
    (i : h.CriticalEndpoint) (hb : 3 ≤ h.b) :
    Nat.card (((i.conjugate D.UH).subgroupOf D.H).map
      (QuotientGroup.mk' (pCore 2 D.H))) =
      (i.conjugate D.UH ⊓ D.QH).relIndex (i.conjugate D.UH) := by
  have hle : i.conjugate D.UH ≤ D.H :=
    (map_mono (conjugateSpanBy_mono h.plus_le le_rfl)).trans (i.large_le hb)
  rw [inf_relIndex_left, ← Subgroup.relIndex_subgroupOf (H := D.QH) hle]
  have he : D.QH.subgroupOf D.H = pCore 2 D.H :=
    Subgroup.comap_map_eq_self_of_injective D.H.subtype_injective _
  rw [he]
  symm
  simpa only [QuotientGroup.ker_mk'] using
    Subgroup.relIndex_ker ((i.conjugate D.UH).subgroupOf D.H)
      (QuotientGroup.mk' (pCore 2 D.H))
end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis

namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- Both source denominators retain the same original endpoint and two-cores. -/
theorem source_critical_denominators
    (i : (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab).CriticalEndpoint) :
    commutatorPreimage (conjugateSpanBy (localModule T M) Mc)
        (i.conjugate (conjugateSpanBy (localModule T M) Mc))
        (i.conjugate (centralInvolutions T)) =
      conjugateSpanBy (localModule T M) Mc ⊓ i.conjugate (Mc.pCoreIn 2) ∧
    commutatorPreimage (i.conjugate (conjugateSpanBy (localModule T M) Mc))
        (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T) =
      i.conjugate (conjugateSpanBy (localModule T M) Mc) ⊓ Mc.pCoreIn 2 := by
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab
    Mc (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
  exact i.denominators _ hb

/-- Quadraticity of the literal source actor on the supplied actual quotient action. -/
theorem source_critical_quadratic
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) (Mc ⧸ pCore 2 Mc) E)
    (c : Representation.BinaryConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) (σ.comp (QuotientGroup.mk' (pCore 2 Mc))))
    (i : (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab).CriticalEndpoint) :
    Representation.BinaryOffender.IsQuadratic σ
      (((i.conjugate (conjugateSpanBy (localModule T M) Mc)).subgroupOf Mc).map
        (QuotientGroup.mk' (pCore 2 Mc))) := by
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab
    Mc (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
  exact i.quadratic _ hb rfl hab σ _ c
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
