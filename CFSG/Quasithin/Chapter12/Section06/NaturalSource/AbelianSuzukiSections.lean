module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianModels
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.ExchangedRecognition

/-!
# The actual Suzuki module sections in the abelian component sieve

The original edge-core quadratic actor acts faithfully on K₀-star in the
literal U_H/V₁. For a normal Suzuki component, saturation of the quadratic
bound identifies the full moved space modulo its fixed space with the
natural Suzuki module. For an exchanged component, its actual index-two
normalizer gives the pair geometry and two independent natural factors.
Both conclusions include an equivariant group and linear isomorphism.

The representation is the prescribed conjugation action: uniqueness of
LocalQuotientAction identifies it with the action carrying the bounded
quadratic witness. The intrinsic K/O₂(K) model is transported by the
literal component-star equivalence. No complement to the fixed space, or
equality of the moved space with U_H/V₁, is imposed.

Source: Aschbacher--Smith 12.6.31, printed p.836, Suzuki paragraph;
F.9.18(4i),(5iiia),(7), printed pp.325--326.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components Chapter13.Section08.Components.SourceModels
open Chapter13.Section08.Components.Suzuki
open Chapter13.Section08.Components.Suzuki.NaturalSections
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
open Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)
  [IsElementaryAbelian 2 ((D.fullSetup hZ T z).UH H)]
  (a : LocalQuotientAction H ((D.fullSetup hZ T z).UH H) (D.fullSetup hZ T z).V₁)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The full moved central section on the original reduced actor has one
natural Suzuki factor or two independent natural factors. -/
theorem SourceHypothesis.original_abelian_suzuki_sections
    {m : ℕ} (hm : 0 < m)
    (eK : (K ⧸ pCore 2 K) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    let K₀ := actorImage H (conjugateSpanBy K (T : Subgroup G))
    let W := subspaceCommutator a.representation ⊤ K₀
    ((K.subgroupOf H).Normal ∧
      Nonempty (ActionEquiv (centralQuotientRepresentation a.representation K₀ W
        (subspaceCommutator_invariant a.representation ⊤ K₀)) (natural m))) ∨
    (¬ (K.subgroupOf H).Normal ∧ (normalizer (K.subgroupOf H : Set H)).index = 2 ∧
      Nonempty (ActionEquiv (centralQuotientRepresentation a.representation K₀ W
        (subspaceCommutator_invariant a.representation ⊤ K₀)) (naturalPair m))) := by
  classical
  obtain ⟨hcomp,hU,b,B,_,hBT,hE,hquad,hcodim,hfaith,_⟩ :=
    S.original_abelian_component_span_actors D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen
  have heq := b.representation_eq a
  rw [heq] at hquad hcodim
  let : IsQuasisimple (actorImage H K) := hcomp.2
  let e : actorImage H K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m :=
    (componentStarEquiv H K hKH hK).symm.trans eK
  have hs := S.original_star_sqtk D hZ z hz hH
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  by_cases hn : (K.subgroupOf H).Normal
  · refine Or.inl ⟨hn,?_⟩
    let : (actorImage H K).Normal := hn.map _ (QuotientGroup.mk'_surjective (pCore 2 H))
    have ho := conjugateSpan_eq_of_normal H K T hKH hTH hn
    rw [ho] at hfaith ⊢
    have hnact : ¬ actorImage H K ≤ a.representation.ker := by
      intro hh
      let : IsSimpleGroup ((actorImage H K) ⧸ center (actorImage H K)) := IsQuasisimple.simple
      let : Nontrivial (actorImage H K) :=
        (QuotientGroup.mk'_surjective (center (actorImage H K))).nontrivial
      exact (nontrivial_iff_ne_bot _).mp inferInstance
        (bot_unique (hh.trans ((MonoidHom.ker_eq_bot_iff _).mpr a.faithful).le))
    exact SourceRecognition.natural_moved_of_quadratic_actor a.representation
      (actorImage H K) (B.map (QuotientGroup.mk' (pCore 2 H))) hm e hs
      hE hquad hcodim hfaith hnact
  · obtain ⟨hi,_⟩ := S.original_abelian_nonnormal_component_models D hZ z hz hTV hTz
      hbound hTI hns hH hKH hK hgen hn
    have hmove : ¬ actorImage H T ≤ normalizer (actorImage H K : Set (H ⧸ pCore 2 H)) := by
      intro ht
      let P := (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
      have hd := index_dvd_of_le ht
      rw [hi] at hd
      exact P.not_dvd_index hd
    have hZK := SectionRecognition.center_eq_bot_of_equiv_suzuki e
    have geo := exchanged_geometry_of_index_two (actorImage H K) (actorImage H T)
      hcomp hZK hi hmove
    let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
    refine Or.inr ⟨hn,(cComponent_normalizer_index_quotient hK (pCore 2 H)).symm.trans hi,?_⟩
    have ho : actorImage H (conjugateSpanBy K (T : Subgroup G)) =
        conjugateSpanBy (actorImage H K) (actorImage H T) :=
      star_conjugateSpan H K T hKH hTH
    rw [ho,conjugateSpanBy_eq_iSup_conj] at hfaith ⊢
    exact ExchangedRecognition.exchanged_natural_pair a.representation geo hi
      (le_normalizer_componentOrbit _ _) a.faithful hcomp hs hm e hBT hE hquad hfaith hcodim


end CFSG.Quasithin.Chapter12.Section06
