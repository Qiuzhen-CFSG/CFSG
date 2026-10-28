module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.Sporadic.SourceAction
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.HigmanSims.SectionOrders
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete
public import Theory.GroupTheory.ComponentLocalDirectPowerSection
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ChiTransport

/-!
# The Higman–Sims exclusion in the original E.6.8 setup

The native 4³.L₃(2) normalizer is invariant under the prescribed Sylow
stabilizer. Its characteristic-two lift has a normal section which is an
actual direct power of SL₃(2). The checked order-168 block obstruction and
E.6.7 place that lift in M. Its quotient and two-core show that it is generated
by two-elements. The source residual condition therefore makes the original
involution fix this seed, contradicting the proved fixed-subgroup generation
of HS. All quotient maps and the covering two-kernel are retained.

Source: Aschbacher–Smith, E.6.8, printed p.248 (PDF p.259), and GLS3
Table 5.3m, the 4³.L₃(2) local of HS.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.Sporadic
open Chapter2.ComponentRefinement.HigmanSims
open _root_.Sporadic.LeechRelated.HS
variable {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
variable {T : Sylow 2 G} {M V U L : Subgroup G}

private theorem linearThreeTwo_primeToResidual : primeToResidual 2 LinearThreeTwo = ⊤ := by
  let _ := Atlas.Comparisons.Exceptional.sl3Two_simple
  rcases (inferInstance : (primeToResidual 2 LinearThreeTwo).Normal).eq_bot_or_eq_top with hb | ht
  · have hc := primeToResidual_index_coprime (G := LinearThreeTwo) 2
    rw [hb, index_bot, Matrix.PSL3Two.card_SL] at hc
    norm_num at hc
  · exact ht

/-- The same original E.6.7 placement works for the actual SL₃(2) Levi quotient. -/
theorem seedLift_le_M_of_linearThreeQuotient
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (e : (L ⧸ pCore 2 L) ≃* A) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (P : Subgroup A)
    (hinv : ∀ a : MulAut A, ((S : Subgroup L).map (modelMap e)).map a.toMonoidHom =
      (S : Subgroup L).map (modelMap e) → P.map a.toMonoidHom = P)
    (hP : HasCharacteristicTwo P) (eqP : (P ⧸ pCore 2 P) ≃* LinearThreeTwo) :
    seedLift e P ≤ M := by
  let Q := sylowCentralizer (T : Subgroup G) V
  have hQ : Q ≤ centralizer (U : Set G) := inf_le_right.trans (centralizer_le hU.1)
  have htwo : IsPGroup 2 Q := T.isPGroup'.to_le inf_le_left
  have hn := seedLift_stable e S hS P hinv
  have hp := seedLift_characteristicTwo e P hP
  have hjoin : HasCharacteristicTwo (seedLift e P ⊔ Q : Subgroup G) := by
    apply (inf_centralizer_pCoreIn_le_iff 2 _).mp
    exact hL.2.relative_local_adjoin_centralizer hL.1 (seedLift_le e P) hQ htwo hn
      ((inf_centralizer_pCoreIn_le_iff 2 _).mpr hp)
  let eqLift := (ComponentLocalCoreSection.quotientCoreEquiv 2 (seedProjection e P)
    (seedProjection_surjective e P) (seedProjection_ker_two e P)).trans eqP
  obtain ⟨sectionData⟩ := hL.2.relative_local_adjoin_normalDirectPowerSection hL.1
    (seedLift_le e P) hQ htwo hn hp eqLift
  obtain ⟨d⟩ := h67 U hU _ le_sup_right
    (sup_le ((seedLift_le e P).trans hL.1) hQ) hjoin
  apply le_sup_left.trans (OtherTypes.le_of_blockDecomposition d ?_)
  intro B hB hs hb
  let b := subgroupOfEquivOfLe hB
  have hb' := hb.of_mulEquiv b.symm
  exact not_chiZero_of_normalDirectPowerSection linearThreeSectionOrders sectionData
    (B.subgroupOf _) ⟨inferInstance, hb'.chi.short, hs⟩ hb'

/-- The native seed's simple even quotient and two-kernel give its full residual. -/
theorem primeToResidual_top_of_linearThreeQuotient {P : Type*} [Group P] [Finite P]
    (e : (P ⧸ pCore 2 P) ≃* LinearThreeTwo) : primeToResidual 2 P = ⊤ := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P))
  apply primeToResidual_top_of_two_kernel f
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) _ linearThreeTwo_primeToResidual
  have he : f.ker = pCore 2 P := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  rw [he]
  exact pCore_isPGroup

variable {K : GroupClass} {z : G}
open Chapter15.Section03.Candidates.ComponentStructure

/-- The HS row of the literal sporadic model/action alternative is impossible
under the original E.6.1 and E.6.7 hypotheses. -/
theorem higmanSims_excluded (h : HypothesisE61 K T M V)
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hz : z ∈ sylowFixedSpace (T : Subgroup G) V)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (ha : TwoCentralInner α) (e : (L ⧸ pCore 2 L) ≃* Carrier) : False := by
  obtain ⟨S,hS⟩ := component_sylow_intersection h hU hL
  let R := S.mapSurjective (f := modelMap e) (modelMap_surjective e)
  let a := modelAction e α
  have ho : orderOf a = 2 :=
    (orderOf_injective (modelAction e) (modelAction_injective hL e) α).trans ha.2.1
  have hi : a ∈ (MulAut.conj (G := Carrier)).range := by
    obtain ⟨l,hl⟩ := ha.1
    exact ⟨modelMap e l, by dsimp [a]; rw [← hl, modelAction_conj]⟩
  obtain ⟨s⟩ := BlockNormalizer.geometry.seed R a ho hi
    (modelAction_fixed_sylow e hz α hα S hS)
  have hplace := seedLift_le_M_of_linearThreeQuotient h67 hU hL e S hS
    s.localSubgroup s.invariant s.selfCentralizing s.quotientIso
  exact false_of_seedLift_and_generation hU hL e s.localSubgroup hplace
    (primeToResidual_top_of_linearThreeQuotient s.quotientIso) hz.1 α hα ha.2.1 s.generated

end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.Sporadic
