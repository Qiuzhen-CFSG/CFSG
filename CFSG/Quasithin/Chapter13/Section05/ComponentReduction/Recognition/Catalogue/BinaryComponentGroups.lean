module
public import Theory.Representation.BinaryOffender.CubicCenterChief
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.TripleSix
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.MarkedSourceCatalogue
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels.AlternatingRows.Six
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.BinaryModels
public import Theory.Alternating.OddCentralCovers
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import Theory.SpecificGroups.SU3.TernaryPerfectCover
public import Theory.SpecificGroups.BinaryComponentResidual
public import Theory.Quasithin.NormalTwoRank
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.SourceLocalContainment

/-!
# The original selected binary component is simple and contains L₁

The full source catalogue gives four central quotients. The odd Schur-kernel
bounds remove the centers except possibly a cubic A₆ center. A faithful
chief factor of the original actor detects that center, and the original
outer marked involution contradicts the triple-A₆ displacement bound.

The resulting literal component has three-rank at least two and a two-group
outer automorphism group. The ordinary cubic-residual theorem therefore
makes it normal and places the original L₁ inside the selected component.
No abstract model action or replacement quotient is assumed.

Source: Aschbacher–Smith13.5.21(1), printed p.924 (PDF p.941).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Section08.Source
open CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (K : Subgroup G) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- The actual original actor excludes the cubic center of an A₆ component. -/
theorem source_not_cubic_center (s : Selected D K)
    [(componentCentralizer s h).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G)
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (hcard : Nat.card D.V = 16)
    (c : SourceConfiguration s h D.L₁ le_rfl)
    (e : Khat s h ≃* alternatingGroup (Fin 6))
    (hz : Nat.card (center (starImage D.H K)) = 3) : False := by
  classical
  let := s.quasisimple
  let : IsQuasisimple (component D K) := IsQuasisimple.of_mulEquiv TripleSix.componentEquiv.symm
  let : IsSimpleGroup (component D K ⧸ center (component D K)) := IsQuasisimple.simple
  let : Nontrivial (component D K) := (QuotientGroup.mk'_surjective (center (component D K))).nontrivial
  have hc := LocalGeometry.star_V_card_two h hi hu
  have heven := selected_section_even s
  have hnorm := selected_star_local_normalization s h hG hH
  have hVnorm := (s.normalizes_and_commutator h hc heven).1
  let : (component D K).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (starImage D.H K).le_normalizer hVnorm)
  obtain ⟨a,ha,hna⟩ := SetLike.not_le_iff_exists.mp
    (LocalModels.source_six_actor_not_le s h D.L₁ c.proved_prefix c.condition_ii_O23 e)
  obtain ⟨x,hxV,rfl⟩ := ha
  have hxstar : starHom s h x ∈ starImage D.H D.V :=
    mem_map_of_mem _ (show inclusion (s.X_le_H h) x ∈ D.V.subgroupOf D.H from hxV)
  have hx1 : starHom s h x ≠ 1 := by
    intro hh
    apply hna
    have hxC : x ∈ componentCentralizer s h := by
      change starHom s h x ∈ centralizer (starImage D.H K : Set (Hstar D.H))
      rw [hh]
      exact one_mem _
    have hxq : QuotientGroup.mk' (componentCentralizer s h) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hxC
    rw [hxq]
    exact one_mem _
  let v : actor D K := ⟨starHom s h x,(show starImage D.H D.V ≤ actor D K from le_sup_right) hxstar⟩
  have hvorder : orderOf (v : Hstar D.H) = 2 := by
    have hd := orderOf_dvd_natCard (⟨v,hxstar⟩ : starImage D.H D.V)
    rw [hc] at hd
    have hh : orderOf (⟨v,hxstar⟩ : starImage D.H D.V) = 2 :=
      ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (fun hh =>
        hx1 (congrArg Subtype.val (orderOf_eq_one_iff.mp hh)))
    exact (orderOf_injective _ (starImage D.H D.V).subtype_injective _).trans hh
  have hv : zpowers (v : Hstar D.H) = starImage D.H D.V :=
    eq_of_le_of_card_ge (zpowers_le.mpr hxstar) (by rw [Nat.card_zpowers,hvorder,hc])
  have hv2 : v ^ 2 = 1 := by
    apply Subtype.ext
    change (v : Hstar D.H) ^ 2 = 1
    simpa only [hvorder] using pow_orderOf_eq_one (v : Hstar D.H)
  have hr : Module.finrank (ZMod 2)
      (LinearMap.range (Action.starRepresentation D h (v : Hstar D.H) - 1)) = 2 := by
    change Module.finrank (ZMod 2)
      (LinearMap.range (Action.starRepresentation D h (v : Hstar D.H) - LinearMap.id)) = 2
    rw [←fixedCodim_zpowers_eq_displacement_rank,hv,sourceRepresentation_eq h]
    exact Fitting.SourceAction.source_fixedCodim_two h hi hu hcard
  have hzC : Nat.card (center (component D K)) = 3 :=
    (Nat.card_congr (centerCongr TripleSix.componentEquiv).toEquiv).trans hz
  obtain ⟨U,N,hirr,hfaith⟩ := exists_faithful_chief_of_cubic_center
    (representation D K h) (component D K) (representation_injective D K h) hzC
  let σ := chiefRepresentation D K h U N
  have hn : ¬ component D K ≤ σ.ker := by
    intro hh
    have hs : Subsingleton (component D K) := ⟨fun a b =>
      hfaith ((hh a.property).trans (hh b.property).symm)⟩
    exact not_subsingleton (component D K) hs
  have hyp := source_chief_hypotheses_all D K h s hG hH hi hu hcard U N hn hirr
  let : IsQuasisimple (generalizedFitting (actionImage σ)) := hyp.quasisimple
  have hfit := image_component_eq_fitting σ (component D K) hn
  have hdr := fixedCodim_section_le (representation D K h) U N (zpowers v)
  rw [fixedCodim_zpowers_eq_displacement_rank,fixedCodim_zpowers_eq_displacement_rank] at hdr
  have hic := PerfectInvolutionExtension.restriction_irreducible σ hirr (component D K)
    hn v (source_actor_generation D K v hv) (hdr.trans hr.le)
  exact TripleSix.excluded_section_of_fullCatalogue D K h s hz
    ((KhatEquiv s h).symm.trans e) hnorm hc heven v hv hv2 x rfl hna hr.le U N
    hic hfaith hfit
    (faithful_section_preparation D K h s hc heven v hv hv2 hr U N hn).2.1
    (source_chief_fullCatalogue D K h s hG hH hi hu hcard U N hn hirr)
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue

namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
open Subgroup Theory.GroupTheory
open Section08.Source
open CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
open PerfectCentralCovering ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (K : Subgroup G) (h : D.Hypothesis)

/-- The four source quotient models force the selected component itself to be centerless. -/
theorem source_component_center_eq_bot_of_binary_models (s : Selected D K)
    [(componentCentralizer s h).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G)
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (hcard : Nat.card D.V = 16)
    (c : SourceConfiguration s h D.L₁ le_rfl)
    (hm : BinaryComponentModels (Khat s h)) : center (starImage D.H K) = ⊥ := by
  let := s.quasisimple
  have hcore : pCore 2 (starImage D.H K) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 s.star_component.1,
      pCore_quotient_pCore_eq_bot 2,MonoidHom.comap_bot]
    exact (MonoidHom.ker_eq_bot_iff _).mpr (starImage D.H K).subtype_injective
  have hodd := GLS3.Chapter5.OddCentralCovers.component_center_odd
    (pCore_quotient_pCore_eq_bot 2) _ s.star_component
  unfold BinaryComponentModels at hm
  rcases hm with hm | hm | hm | hm <;> obtain ⟨e⟩ := hm
  · rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide)
      ((KhatEquiv s h).symm.trans e) hodd with hz | ⟨_,hz⟩
    · exact (eq_bot_iff_card _).mpr hz
    · let := Action.point_normal D h
      let := Action.quotient_elementary D h
      exact (source_not_cubic_center D K h s hG hH hi hu hcard c e hz).elim
  · have hh := GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 8 (by decide)
      ((KhatEquiv s h).symm.trans e) hodd
    exact (eq_bot_iff_card _).mpr (hh.resolve_right (by omega))
  · exact center_eq_bot_of_centralQuotientEquiv
      (Theory.SpecificGroups.PSL5Two.UniversalCover.field_universalProjection_ker_eq_bot
        (ZMod 2) (by simp))
      (((KhatEquiv s h).symm.trans e).trans (binaryProjectiveEquiv 5 (by decide)))
  · let f := centralQuotientCover ((KhatEquiv s h).symm.trans e)
    have hf := HermitianForm.TernaryPerfectCover.binaryDerived_kernel_isTwoGroup f
    have hk : f.toMonoidHom.ker ≤ pCore 2 (starImage D.H K) := le_sSup ⟨inferInstance,hf⟩
    simpa only [f,centralQuotientCover_ker,hcore] using le_bot_iff.mp (hk.trans hcore.le)

/-- The actual source configuration supplies the full binary shortlist. -/
theorem source_component_center_eq_bot (s : Selected D K)
    [(componentCentralizer s h).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G)
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (hcard : Nat.card D.V = 16)
    (c : SourceConfiguration s h D.L₁ le_rfl) : center (starImage D.H K) = ⊥ := by
  let := Action.point_normal D h
  let := Action.quotient_elementary D h
  exact source_component_center_eq_bot_of_binary_models D K h s hG hH hi hu hcard c
    (source_binary_component_models D K h s hG hH hi hu hcard D.L₁ le_rfl c)

/-- Centerlessness recovers simplicity on the literal star-image carrier. -/
theorem source_component_simple (s : Selected D K)
    [(componentCentralizer s h).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G)
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (hcard : Nat.card D.V = 16)
    (c : SourceConfiguration s h D.L₁ le_rfl) : IsSimpleGroup (starImage D.H K) := by
  let := s.quasisimple
  let : IsSimpleGroup (starImage D.H K ⧸ center (starImage D.H K)) := IsQuasisimple.simple
  exact (((QuotientGroup.quotientMulEquivOfEq
    (source_component_center_eq_bot D K h s hG hH hi hu hcard c)).trans
      QuotientGroup.quotientBot).symm).isSimpleGroup

/-- The same literal model comparison provides the source rank and outer-group facts. -/
theorem source_component_binary_facts (s : Selected D K)
    [(componentCentralizer s h).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G)
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (hcard : Nat.card D.V = 16)
    (c : SourceConfiguration s h D.L₁ le_rfl) :
    Theory.SpecificGroups.BinaryComponentResidual.Facts (starImage D.H K) := by
  let := Action.point_normal D h
  let := Action.quotient_elementary D h
  have hm := source_binary_component_models D K h s hG hH hi hu hcard D.L₁ le_rfl c
  have hz := source_component_center_eq_bot_of_binary_models D K h s hG hH hi hu hcard c hm
  let q : starImage D.H K ≃* Khat s h :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.trans
      (KhatEquiv s h).symm
  unfold BinaryComponentModels at hm
  rcases hm with hm | hm | hm | hm <;> obtain ⟨e⟩ := hm
  · exact Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv (q.trans e)
      Theory.SpecificGroups.BinaryComponentResidual.alternatingSix
  · let a := (binaryProjectiveEquiv 4 (by decide)).trans
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
    exact Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv
      ((q.trans e).trans a.symm) (Theory.SpecificGroups.BinaryComponentResidual.linear (Or.inl rfl))
  · exact Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv (q.trans e)
      (Theory.SpecificGroups.BinaryComponentResidual.linear (Or.inr rfl))
  · exact Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv (q.trans e)
      Theory.SpecificGroups.BinaryComponentResidual.g2

/-- D13.5.21(1): the original cubic local residual lies in the selected component. -/
theorem source_local_le_component (s : Selected D K)
    [(componentCentralizer s h).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G)
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (hcard : Nat.card D.V = 16)
    (c : SourceConfiguration s h D.L₁ le_rfl)
    (hc : Nat.card (D.L₁ ⧸ pCore 2 D.L₁) = 3) : D.L₁ ≤ K ∧ (K.subgroupOf D.H).Normal := by
  have hf := source_component_binary_facts D K h s hG hH hi hu hcard c
  have hcore : pCore 2 D.H ≠ ⊥ := by
    intro he
    apply hH
    change (pCore 2 D.H).map D.H.subtype = ⊥
    rw [he,Subgroup.map_bot]
  have hr := Theory.Quasithin.primeRank_subgroup_le_two_of_normal_two_subgroup
    hG.quasithin D.H (pCore 2 D.H) hcore pCore_isPGroup 3 Nat.prime_three (by decide)
  exact s.local_le_of_binary_component h hc hf.1 hf.2.1 hr hf.2.2
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
