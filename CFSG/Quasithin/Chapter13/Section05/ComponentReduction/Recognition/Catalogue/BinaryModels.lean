module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.ChiefSieve
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.SourceUnitary
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.TripleSix
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section

/-!
# The four binary component quotients in 13.5.21

The faithful action on a noncentral chief section has a genuine involution
of displacement at most two. The complete chief catalogue, the original
configuration exclusions, and the marked sporadic and exceptional exclusions
leave A₆, A₈, SL₅(2), and G₂(2)′ as the component-centralizer quotients.

A noncentral chief section is selected from the original faithful action
using perfectness. Thus the source theorem has no chief-existence or
classification premise. Centerlessness, local containment, and the final
natural-module recognition are subsequent source steps.

Source: Aschbacher–Smith, 13.5.21, printed pp.923–924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue

@[expose] def BinaryComponentModels (L : Type*) [Group L] : Prop :=
  Nonempty (L ≃* alternatingGroup (Fin 6)) ∨
  Nonempty (L ≃* alternatingGroup (Fin 8)) ∨
  Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∨
  Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2)))

private def quotientModel {L M : Type*} [Group L] [Group M]
    (e : L ≃* M) (hz : center M = ⊥) : (L ⧸ center L) ≃* M :=
  (Representation.TripleSixOuterDisplacement.centralQuotientEquiv e).trans
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot)

private theorem binary_models_linear {L : Type*} [Group L] {d : ℕ}
    (hd : d = 4 ∨ d = 5) (e : L ≃* Matrix.SpecialLinearGroup (Fin d) (ZMod 2)) :
    BinaryComponentModels (L ⧸ center L) := by
  rcases hd with rfl | rfl
  · exact Or.inr (Or.inl ⟨(quotientModel e (sl_binary_center_eq_bot 4 (by decide))).trans
      ((binaryProjectiveEquiv 4 (by decide)).trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨quotientModel e (sl_binary_center_eq_bot 5 (by decide))⟩))

private theorem quadratic_of_marked {E W : Type*} [Group E] [Finite E]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) E W) (t : E) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2) : quadraticRatio ρ ≤ 2 := by
  obtain ⟨hA,hrank,hquad,_⟩ := involution_actor_rank_and_fixedCodim ρ t ht
  apply (quadraticRatio_le_two_iff ρ).mpr
  refine ⟨zpowers t,hA,hquad,?_⟩
  rw [hrank,fixedCodim_zpowers_eq_displacement_rank]
  exact hr

/-- The complete marked chief catalogue leaves exactly the four simple binary
component quotients needed before the source local-containment argument. -/
theorem binary_models_of_chief_sieve {E W : Type*} [Group E] [Finite E]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) E W)
    (hyp : Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.B4Hypotheses
      KnownSimple.IsKnownSimple ρ)
    (c : ChiefSieve ρ)
    (unitary : ∀ (F : BinaryField) (n : ℕ), 2 ≤ n → F.degree = 2*n →
      ∀ J : BenderSuzuki.MatrixGroups.HermitianForm 3 F.Carrier, ¬ UnitaryChiefAction ρ F J)
    (t : E) (ht : orderOf t = 2)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) ≤ 2) :
    BinaryComponentModels (generalizedFitting E ⧸ center (generalizedFitting E)) := by
  have hq := quadratic_of_marked ρ t ht hr
  have hs := ChapterB.SmallRatioClassification.rankOne_source_of_b4_quadratic hyp hq
  have hspor : ∀ e : (generalizedFitting E ⧸ center (generalizedFitting E)) ≃* Sporadic.Mathieu.M22,
      False := by
    classical
    intro e
    exact ChapterB.SmallRatioClassification.sporadic_false_of_marked_involution hs
      (Or.inl ⟨.m22,(by intro he; cases he),⟨e⟩⟩) t ht (by
        rw [fixedCodim_zpowers_eq_displacement_rank]
        exact hr)
  rcases c.catalogue with h | h
  · cases h with
    | linearTwo F _ e _ _ => exact (c.not_linearTwo F ⟨e⟩).elim
    | linearThree F _ e _ => exact (c.not_linearThree F ⟨e⟩).elim
    | symplectic F large _ e _ => exact (c.not_symplectic F large ⟨e⟩).elim
    | symplecticTwo e _ =>
      exact Or.inl ⟨quotientModel (e.subgroupEquiv.trans binarySymplecticDerivedEquiv)
        (alternatingGroup.center_eq_bot (by simp))⟩
    | g2 F large _ e _ _ =>
      have hF : 2 < Nat.card F.Carrier := by
        rw [F.card_eq]
        have hh := Nat.pow_lt_pow_right (by decide : 1 < 2) large
        simpa using hh
      exact (ChapterB.SmallRatioClassification.g2_excluded_of_small_involution hs F large
        (quotientModel e.groupEquiv (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hF))
        t ht hr).elim
    | g2Two e _ _ =>
      exact Or.inr (Or.inr (Or.inr ⟨quotientModel e.subgroupEquiv
        Theory.SpecificGroups.g2_derived_two_center_eq_bot⟩))
    | symmetric n degree e _ _ =>
      rcases degree with rfl | rfl
      · exact (c.not_five ⟨e.subgroupEquiv⟩).elim
      · exact (c.not_seven ⟨e.subgroupEquiv⟩).elim
    | alternatingSix _ e _ _ =>
      exact Or.inl ⟨quotientModel e.groupEquiv (alternatingGroup.center_eq_bot (by simp))⟩
    | alternatingSeven _ _ e _ _ _ => exact (c.not_seven ⟨e⟩).elim
    | tripleSix _ a _ => exact Or.inl ⟨a.quotientEquiv⟩
    | binaryLinear d hd _ e _ => exact binary_models_linear hd e.groupEquiv
    | orthogonalSix _ _ e _ _ =>
      exact Or.inr (Or.inl ⟨quotientModel e.groupEquiv (alternatingGroup.center_eq_bot (by simp))⟩)
    | symmetricEight _ e _ =>
      exact Or.inr (Or.inl ⟨quotientModel e.subgroupEquiv (alternatingGroup.center_eq_bot (by simp))⟩)
    | exteriorFive _ _ e _ _ _ => exact binary_models_linear (Or.inr rfl) e
  · cases h with
    | alternatingSeven e _ _ _ => exact (c.not_seven ⟨e.groupEquiv⟩).elim
    | orthogonal K F degree e _ _ _ _ => exact (c.not_orthogonal K F degree ⟨e⟩).elim
    | unitary F n large degree J _ e _ _ _ => exact (unitary F n large degree J ⟨e⟩).elim
    | suzuki k hk e _ _ _ => exact (c.not_suzuki k hk ⟨e⟩).elim
    | linearThree _ _ _ _ _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim
    | g2Derived e _ _ _ =>
      exact Or.inr (Or.inr (Or.inr ⟨quotientModel e.groupEquiv
        Theory.SpecificGroups.g2_derived_two_center_eq_bot⟩))
    | mathieuTwelve _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim
    | tripleMathieuTwentyTwo _ e _ _ _ => exact (hspor e).elim
    | mathieuTwentyTwoCocode _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim
    | mathieuTwentyTwoCode e _ _ _ =>
      exact (hspor (quotientModel e.groupEquiv Sporadic.Mathieu.m22_center_eq_bot)).elim
    | mathieuTwentyThreeCocode _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim
    | mathieuTwentyThreeCode _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim
    | mathieuTwentyFourCocode _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim
    | mathieuTwentyFourCode _ _ hbad _ => exact (not_lt_of_ge hq hbad).elim

theorem BinaryComponentModels.of_mulEquiv {L M : Type*} [Group L] [Group M]
    (e : L ≃* M) (h : BinaryComponentModels M) : BinaryComponentModels L := by
  rcases h with h | h | h | h <;> obtain ⟨f⟩ := h
  · exact Or.inl ⟨e.trans f⟩
  · exact Or.inr (Or.inl ⟨e.trans f⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans f⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨e.trans f⟩))

open Section08.Source
open CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration
variable {G : Type*} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (K : Subgroup G) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
  (s : Selected D K) [(componentCentralizer s h).Normal]

/-- Every original noncentral chief section gives the same four possible
simple quotients for the literal component-centralizer quotient. -/
theorem source_chief_binary_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G)
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (hcard : Nat.card D.V = 16)
    (U N : Subrepresentation (representation D K h))
    (hn : ¬ component D K ≤ (chiefRepresentation D K h U N).ker)
    (hirr : IsIrreducible (chiefRepresentation D K h U N))
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY) :
    BinaryComponentModels (Khat s h) := by
  have hyp := source_chief_hypotheses_all D K h s hG hH hi hu hcard U N hn hirr
  have sieve := source_chief_sieve D K h s hG hH hi hu hcard U N hn hirr Y hY c
  obtain ⟨t,ht,hr,_⟩ := source_chief_marked_all D K h s hG hH hi hu hcard U N hn hirr
  have hm := binary_models_of_chief_sieve _ hyp sieve
    (fun F n hn' hdeg J => source_chief_not_unitary D K h s hG hH hi hu hcard
      U N hn hirr F n hn' hdeg J) t ht hr
  obtain ⟨comparison⟩ := source_chief_comparison D K h s hG hH hi hu hcard U N hn hirr
  exact hm.of_mulEquiv comparison

private theorem exists_noncentral_chief
    {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) E W)
    (L : Subgroup E) [Group.IsPerfect L] (hn : ¬ L ≤ ρ.ker) :
    ∃ U N : Subrepresentation ρ,
      IsIrreducible (sectionRepresentation ρ U N) ∧
      ¬ L ≤ (sectionRepresentation ρ U N).ker := by
  obtain ⟨N,U,hi,hn⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect L hn
  let P : Subrepresentation ρ := {
    toSubmodule := U.toSubmodule.map N.toSubmodule.subtype
    apply_mem_toSubmodule g v hv := by
      obtain ⟨u,hu,rfl⟩ := hv
      exact ⟨N.toRepresentation g u,U.apply_mem_toSubmodule g hu,rfl⟩ }
  have he : sectionLower ρ P N = U := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.comap_map_eq_of_injective N.toSubmodule.subtype_injective _
  refine ⟨P,N,?_⟩
  change IsIrreducible (sectionLower ρ P N).quotientRepresentation ∧
    ¬ L ≤ (sectionLower ρ P N).quotientRepresentation.ker
  rw [he]
  exact ⟨hi,hn⟩

/-- Select an actual noncentral chief section; no existence or model premise
remains in the source quotient shortlist. -/
theorem source_binary_component_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hH : D.H ∈ Chapter1.H G)
    (hi : D.Vplus.relIndex D.V = 2) (hu : ¬ IsMulCommutative D.UH)
    (hcard : Nat.card D.V = 16)
    (Y : Subgroup G) (hY : Y ≤ D.L₁) (c : SourceConfiguration s h Y hY) :
    BinaryComponentModels (Khat s h) := by
  let : IsQuasisimple (starImage D.H K) := s.quasisimple
  let : IsQuasisimple (component D K) := IsQuasisimple.of_mulEquiv
    (subgroupOfEquivOfLe (show starImage D.H K ≤ actor D K from le_sup_left)).symm
  have hn : ¬ component D K ≤ (representation D K h).ker := by
    intro hz
    have hk : starImage D.H K = ⊥ := by
      apply bot_unique
      intro k hk
      have he := (representation_injective D K h)
        ((hz (show (⟨k,(show starImage D.H K ≤ actor D K from le_sup_left) hk⟩ : actor D K)
          ∈ component D K from hk)).trans (map_one _).symm)
      exact congrArg Subtype.val he
    exact s.moved (by rw [hk]; simp)
  obtain ⟨U,N,hirr,hn⟩ := exists_noncentral_chief (representation D K h) (component D K) hn
  exact source_chief_binary_models D K h s hG hH hi hu hcard U N hn hirr Y hY c

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue
