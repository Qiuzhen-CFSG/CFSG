module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.Selection
/-!
# Rank transport under the same critical-endpoint reversal

The genuine F.9 reversal carries every invariant label by one conjugator.
Mapping the two literal opposite-core intersections exchanges their indices;
the first isomorphism theorem identifies these with the star-actor orders.
A rank-compared endpoint again belongs to the quadratic family, so the
point-placement argument can be applied after the equal-rank reversal.

Source: Aschbacher--Smith F.9.17 and 14.6.24(3), printed pp.324,1041.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Chapter13.Section08 Chapter13.Section08.CriticalGeometry
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- Every rank-compared endpoint is in the quadratic family, including
the reversed endpoint used in the equality case. -/
@[expose] def quadraticEndpointOfComparison
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (i : h.CriticalEndpoint) (hb : 3 ≤ h.b) (hplus : D.Vplus = D.V)
    [IsElementaryAbelian 2 D.UH]
    {ρ : Representation (ZMod 2) (D.H ⧸ pCore 2 D.H) E}
    (c : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (hcmp : Nat.log 2 ((D.UH ⊓ i.conjugate D.QH).relIndex D.UH) ≤
      rank (((i.conjugate D.UH).subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H)))) :
    QuadraticEndpoint h ρ := by
  have hp := i.denominator_positive h hb hplus
  have hUV : D.UH = D.VH := by
    change conjugateSpanBy D.Vplus D.H = conjugateSpanBy D.V D.H
    rw [hplus]
  let : IsElementaryAbelian 2 (i.conjugate D.UH) := IsElementaryAbelian.map _
  have hAH : i.conjugate D.UH ≤ D.H := by
    rw [hUV]
    exact i.large_le hb
  have he := starImage_isElementaryAbelian D.H (i.conjugate D.UH) hAH
  have hn : Source.starImage D.H (i.conjugate D.UH) ≠ ⊥ := by
    intro hz
    change Nat.log 2 ((D.UH ⊓ i.conjugate D.QH).relIndex D.UH) ≤
      rank (Source.starImage D.H (i.conjugate D.UH)) at hcmp
    rw [hz] at hcmp
    have hr : rank (⊥ : Subgroup (Source.Hstar D.H)) = 0 := by simp [rank]
    rw [hr] at hcmp
    omega
  have hbound := endpoint_fixedCodim_le_rank_add_denominator h i hb c
  refine ⟨i,hp,hcmp,⟨hn,he⟩,?_,by omega⟩
  exact i.quadratic h hb hUV inferInstance ρ _ c
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents

namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Chapter13.Section08 Chapter13.Section08.CriticalGeometry
variable {G : Type*} [Group G] [Finite G]

/-- Reversing exchanges the two literal ranks and transports every invariant
label by the same group element. No coordinate isomorphism is substituted
for either quotient map. -/
theorem endpoint_reverse_indices
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (i : h.CriticalEndpoint) (hb : 3 ≤ h.b) (hn : ¬ i.conjugate D.UH ≤ D.QH) :
    ∃ j : h.CriticalEndpoint,
      (∀ A : Subgroup G, D.H ≤ normalizer (A : Set G) →
        j.conjugate (i.conjugate A) = A) ∧
      Nat.log 2 ((D.UH ⊓ j.conjugate D.QH).relIndex D.UH) =
        rank (((i.conjugate D.UH).subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H))) ∧
      rank (((j.conjugate D.UH).subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H))) =
        Nat.log 2 ((D.UH ⊓ i.conjugate D.QH).relIndex D.UH) := by
  obtain ⟨j,hj⟩ := i.reverse_labels hb hn
  have hU := hj D.UH (le_normalizer_conjugateSpanBy _ _)
  have hQ := hj D.QH (D.H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image D.H (pCore 2 D.H)))
  refine ⟨j,hj,?_,?_⟩
  · have he := relIndex_map_map_of_injective (f := (MulAut.conj j.representative).toMonoidHom) (i.conjugate D.UH ⊓ D.QH)
      (i.conjugate D.UH) (MulAut.conj j.representative).injective
    rw [map_inf _ _ _ (MulAut.conj j.representative).injective,hU] at he
    rw [rank,i.actor_card h hb]
    exact congrArg (Nat.log 2) he
  · have he := relIndex_map_map_of_injective (f := (MulAut.conj j.representative).toMonoidHom) (D.UH ⊓ i.conjugate D.QH)
      D.UH (MulAut.conj j.representative).injective
    rw [map_inf _ _ _ (MulAut.conj j.representative).injective,hQ] at he
    rw [rank,j.actor_card h hb]
    exact congrArg (Nat.log 2) he
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents

namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]

/-- Nontriviality of the selected literal star image supplies the hypothesis
required by the actual endpoint reversal theorem. -/
theorem QuadraticEndpoint.not_le_core
    {D : ChapterF.Section09.Setup G} {h : D.Hypothesis}
    {ρ : Representation (ZMod 2) (D.H ⧸ pCore 2 D.H) E}
    (p : QuadraticEndpoint h ρ) : ¬ p.endpoint.conjugate D.UH ≤ D.QH := by
  intro hle
  apply p.member.1.1
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [QuotientGroup.ker_mk']
  have he : D.QH.subgroupOf D.H = pCore 2 D.H :=
    Subgroup.comap_map_eq_self_of_injective D.H.subtype_injective _
  rw [← he]
  exact comap_mono hle

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- On the original terminal group, a selected actor always has a genuine
reverse endpoint. The two numerical quantities are exchanged, and every
Mc-invariant subgroup uses the same reverse conjugator. -/
theorem source_selected_endpoint_reverse
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    {ρ : Representation (ZMod 2) (Mc ⧸ pCore 2 Mc) E}
    (p : QuadraticEndpoint
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) ρ) :
    let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    let U := conjugateSpanBy (localModule T M) Mc
    ∃ j : h.CriticalEndpoint,
      (∀ A : Subgroup G, Mc ≤ normalizer (A : Set G) →
        j.conjugate (p.endpoint.conjugate A) = A) ∧
      Nat.log 2 ((U ⊓ j.conjugate (Mc.pCoreIn 2)).relIndex U) =
        rank (((p.endpoint.conjugate U).subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) ∧
      rank (((j.conjugate U).subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) =
        Nat.log 2 ((U ⊓ p.endpoint.conjugate (Mc.pCoreIn 2)).relIndex U) := by
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab
    Mc (ComponentSupports.terminal_outside hG T hempty hM hunique hmany hcard e)
  exact endpoint_reverse_indices _ p.endpoint hb p.not_le_core
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
