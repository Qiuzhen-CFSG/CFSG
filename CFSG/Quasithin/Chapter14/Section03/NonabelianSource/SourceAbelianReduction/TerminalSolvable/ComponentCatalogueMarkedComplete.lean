module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeMathieu
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeBinaryFour
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeTensor
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeTripleSix
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeSymplectic
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeLinearThree
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeRankOne
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeEvenExclusions
/-!
# Complete recognition of the original marked constituent images

The literal G.9 carrier catalogue exhausts the single whole component.
Every model exclusion and allowed image is supplied by the proved whole
families, including M₁₂ and binary PSL₄(2). The original nonfaithful and
proper faithful branches and the genuine two-component tensor construction
then close the full marked recognition. No classification or fixed-point
premise is added to MarkedSource.

The resulting ambient-normal component images feed the original local lift
and intrinsic two-core quotient in ComponentCatalogue. The separate exchanged
constituent and terminal-solvability assembly retain their original owners.
Source: Aschbacher–Smith G.9.3, G.10.15(I), G.11.6–9 and 14.3.15.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative MatrixGroups
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

open Module ChapterG.Section09 ChapterG.Section09.DefiningCharacteristic
open Chapter1.Section02.LocalModels

private theorem imageCases_of_single_original (hHL : componentOrbit L ⊤ = L)
    (hm : ComponentOrbitImageCases L L) : s.ImageCases := by
  let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
  let eL := MarkedAction.subgroupEquiv F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
    (s.constituent_faithful R s.irreducible) L (le_componentOrbit L ⊤)
  have he := congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
  rcases hm with ⟨_,hm⟩ | hm | ⟨_,⟨e⟩⟩
  · refine Or.inl ⟨he,?_⟩
    rcases hm with ⟨e⟩ | ⟨e⟩ | ⟨e⟩ | ⟨e⟩
    · exact Or.inl ⟨eL.symm.trans e.some⟩
    · exact Or.inr (Or.inl ⟨eL.symm.trans e.some⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨eL.symm.trans e.some⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨eL.symm.trans e.some⟩))
  · refine Or.inr (Or.inl ?_)
    rcases hm with ⟨e⟩ | ⟨e⟩
    · exact Or.inl ⟨eL.symm.trans e.some⟩
    · exact Or.inr ⟨eL.symm.trans e.some⟩
  · exact Or.inr (Or.inr ⟨he,⟨eL.symm.trans e⟩⟩)

variable (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L)
include hi hHL
private theorem whole_single_hypothesis :
    ComponentHypothesis KnownSimple.IsKnownSimple F.terminalRepresentation
      (F.terminalDot (F.X g)) L L
      (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) := by
  have h := s.componentHypothesis_of_whole hi
  rwa [hHL] at h

private theorem whole_binary_linear {n : ℕ} (hn : n=4 ∨ n=5)
    (model : ClassicalGroup.IsPSL L n 2) : False := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : Fintype k := Fintype.ofFinite k
  let a : k ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hcard)
  rcases hn with rfl | rfl
  · exact s.not_whole_binary_four hi hHL (e.trans (Atlas.fieldEquivPSL 4 a))
  · exact s.not_whole_even_models hi hHL (Or.inr (Or.inr ⟨e.trans (Atlas.fieldEquivPSL 5 a)⟩))

private theorem whole_odd_two {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (model : ClassicalGroup.IsPSL L 2 (p^e)) : s.ImageCases := by
  have h9 := s.whole_single_hypothesis hi hHL
  let : IsQuasisimple L := s.component.2
  let : IsIrreducible (F.terminalRepresentation.comp L.subtype) := h9.irreducible
  rcases ChapterG.Section07.OddCharacteristic.psl2_identification_of_degree_le_automorphism_rank
    (F.terminalRepresentation.comp L.subtype) (h9.faithful.comp L.subtype_injective)
    hp ho he model h9.single_component_degree_bound with hb | ht | he
  · obtain ⟨k,_,_,hcard,⟨e⟩⟩ := hb
    obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hcard
    exact s.imageCases_of_single_original hHL (Or.inr (Or.inl (Or.inl ⟨e.trans a⟩)))
  · exact (s.not_whole_linear_three hi hHL (n := 1) (by decide) (Or.inl (by simpa using ht))).elim
  · exact s.imageCases_of_single_original hHL (Or.inr (Or.inl (Or.inr ⟨he.some.trans
      (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp))⟩)))

private theorem whole_odd_three {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (model : ChapterG.Section07.OddCharacteristic.IsLinearUnitaryThree L p) : s.ImageCases := by
  have h9 := s.whole_single_hypothesis hi hHL
  let : IsQuasisimple L := s.component.2
  let : IsIrreducible (F.terminalRepresentation.comp L.subtype) := h9.irreducible
  obtain ⟨e,_⟩ := ChapterG.Section07.OddCharacteristic.linear_unitary_three_of_degree_le_automorphism_rank
    (F.terminalRepresentation.comp L.subtype) (h9.faithful.comp L.subtype_injective)
    hp ho model h9.single_component_degree_bound
  exact s.imageCases_of_single_original hHL (Or.inl ⟨rfl,Or.inl e⟩)

private theorem whole_alternating {n : ℕ} (hn : 5≤n ∧ n≤8)
    (e : L ≃* alternatingGroup (Fin n)) : s.ImageCases := by
  obtain ⟨hnl,hnu⟩ := hn
  interval_cases n
  · exact s.imageCases_of_single_original hHL (Or.inr (Or.inl (Or.inl ⟨e⟩)))
  · exact s.imageCases_of_single_original hHL (Or.inr (Or.inl (Or.inr ⟨e⟩)))
  · exact s.imageCases_of_single_original hHL (Or.inl ⟨rfl,Or.inr (Or.inl ⟨e⟩)⟩)
  · exact (s.not_whole_alternating_eight hi hHL e).elim

private theorem whole_rank_one (model : ClassificationModels.IsBenderModel L) : s.ImageCases := by
  have h9 := s.whole_single_hypothesis hi hHL
  cases model with
  | linear n hn hm => exact s.imageCases_of_whole_projective_rank_one hi hHL hn hm
  | unitary n hn hm =>
    obtain ⟨k,_,_,J,hcard,hconj,e⟩ := hm
    exact (TwistedExclusions.not_unitary_three_positive_exponent h9 J (by omega) hcard hconj (Or.inr e)).elim
  | suzuki k hk e => exact (h9.not_suzuki hk e.some).elim

private theorem whole_rank_two (model : RankTwoTheoremC L) : s.ImageCases := by
  have h9 := s.whole_single_hypothesis hi hHL
  cases model with
  | linear n hn hm => exact (s.not_whole_linear_three hi hHL hn (Or.inl hm)).elim
  | symplectic n hn hm => exact (s.not_whole_projective_symplectic hi hHL hn hm).elim
  | g2 n hn hm => exact (s.not_whole_full_g2 hi hHL hn hm).elim
  | triality n hn hm => exact (TwistedExclusions.not_triality_positive_exponent h9 hn hm).elim
  | ree k hk hm =>
    obtain ⟨d,e⟩ := hm
    exact (TwistedExclusions.not_ree_of_local_block h9 hk d e.some).elim
  | symplectic_derived e =>
    exact s.imageCases_of_single_original hHL (Or.inr (Or.inl (Or.inr ⟨e.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩)))
  | g2_derived e => exact s.imageCases_of_single_original hHL (Or.inl ⟨rfl,Or.inl e⟩)
  | tits e => exact (TwistedExclusions.not_tits_of_source_component h9 e.some).elim

omit s hi hHL in
private theorem simple_center_eq_bot {S : Type*} [Group S] [IsSimpleGroup S] [Group.IsPerfect S] :
    center S = ⊥ := by
  rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp ht)).elim

private theorem whole_simple_models (hsimple : IsSimpleGroup L) (model : TheoremCModel L) :
    s.ImageCases := by
  have h9 := s.whole_single_hypothesis hi hHL
  let : IsSimpleGroup L := hsimple
  let : IsQuasisimple L := s.component.2
  let q : L ⧸ center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq simple_center_eq_bot).trans QuotientGroup.quotientBot
  cases model with
  | alternating n hn e => exact s.whole_alternating hi hHL hn e.some
  | linear_odd p e hp ho he _ hm => exact s.whole_odd_two hi hHL hp ho (by rcases he with rfl | rfl <;> decide) hm
  | three_odd p hp ho unitary hm =>
    apply s.whole_odd_three hi hHL hp ho
    cases unitary with
    | false => exact Or.inl hm
    | true => exact Or.inr (Or.inr (Or.inl hm))
  | rank_one hm => exact s.whole_rank_one hi hHL hm
  | rank_two hm => exact s.whole_rank_two hi hHL hm
  | binary_linear n hn hm => exact (s.whole_binary_linear hi hHL hn hm).elim
  | sporadic name hne e =>
    cases name with
    | m11 => exact (h9.not_m11_central_quotient (q.trans e.some)).elim
    | m12 => exact (s.not_whole_mathieu_twelve hi hHL e.some).elim
    | m22 => exact s.imageCases_of_single_original hHL (Or.inl ⟨rfl,Or.inr (Or.inr (Or.inl e))⟩)
    | m23 => exact (s.not_whole_even_models hi hHL (Or.inl e)).elim
    | m24 => exact (s.not_whole_even_models hi hHL (Or.inr (Or.inl e))).elim
    | j2 => exact (s.not_whole_janko_two hi hHL e.some).elim
    | j3 => exact (hne rfl).elim
    | j4 => exact (h9.not_janko_four e.some).elim
    | hs => exact (h9.not_higman_sims e.some).elim
    | he => exact (h9.not_held e.some).elim
    | ru => exact (h9.not_rudvalis e.some).elim
  | janko_one e => exact (h9.not_j1_central_quotient (q.trans e.some)).elim

private theorem whole_cover_models (model : ThreeCoverModel L) : s.ImageCases := by
  have h9 := s.whole_single_hypothesis hi hHL
  cases model with
  | classical unitary q hq hm =>
    cases unitary with
    | false =>
      change IsSL L 3 q at hm
      rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
      · exact (s.not_whole_linear_three hi hHL hn (Or.inr hm)).elim
      · exact s.whole_odd_three hi hHL hp ho (Or.inr (Or.inl hm))
    | true =>
      change IsSU L 3 q at hm
      rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
      · obtain ⟨k,_,_,J,hcard,hconj,e⟩ := hm
        exact (TwistedExclusions.not_unitary_three_positive_exponent h9 J hn hcard hconj (Or.inl e)).elim
      · exact s.whole_odd_three hi hHL hp ho (Or.inr (Or.inr (Or.inr hm)))
  | alternating_six hm => exact (s.not_whole_triple_alternating_six hi hHL hm.2.2.some
      ((Nat.card_congr hm.2.1.some.toEquiv).trans (by simp))).elim
  | alternating_seven hm => exact (h9.not_triple_alternating_seven hm.2.2.some
      ((Nat.card_congr hm.2.1.some.toEquiv).trans (by simp))).elim
  | mathieu hm =>
    have hz : Nat.card (center L) = 3 := (Nat.card_congr hm.2.1.some.toEquiv).trans (by simp)
    let : IsQuasisimple L := s.component.2
    obtain ⟨e⟩ := Sporadic.Mathieu.M22TripleCover.nonempty_mulEquiv hz hm.2.2
    exact s.imageCases_of_single_original hHL (Or.inl ⟨rfl,Or.inr (Or.inr (Or.inr ⟨e⟩))⟩)

theorem imageCases_of_whole_single : s.ImageCases := by
  rcases (s.whole_single_hypothesis hi hHL).single_component_models with ⟨hs,hm⟩ | ⟨_,hm⟩
  · exact s.whole_simple_models hi hHL hs hm
  · exact s.whole_cover_models hi hHL hm

omit hi hHL in
/-- Every original marked constituent has one of the actual allowed images.
The proper, nonfaithful, whole-single and genuine whole-tensor branches are
all discharged from the original source data. -/
theorem imageCases : s.ImageCases := by
  apply s.imageCases_of_whole_single_recognition
  intro _ hi hHL _
  exact s.imageCases_of_whole_single hi hHL

omit hi hHL in
/-- The recognized original component retains ambient normality in each
large row, through its literal constituent action image. -/
theorem recognized_componentImageCases : ComponentImageCases L :=
  s.componentImageCases s.imageCases

omit hi hHL in
/-- Unconditional marked-branch input to the original terminal-solvability
assembly, with the actual component lift and intrinsic two-core quotient. -/
theorem local_lift : ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases s.imageCases

omit hi hHL in
/-- The whole two-component branch supplies the genuine tensor action and
the transported original invariant form on the literal dotted span. -/
theorem local_lift_and_form_model_of_whole_pair
    (hi : I = ⊤) (hne : componentOrbit L ⊤ ≠ L) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K ∧
      ∃ m : ExchangedA5.ActionModel F K,
        (m.form B).IsAlt ∧ (m.form B).Nondegenerate ∧
        ∀ a u w, m.form B (ClassicalOrthogonal.FourPlusMatrix.Binary.action a u)
          (ClassicalOrthogonal.FourPlusMatrix.Binary.action a w) = m.form B u w := by
  obtain ⟨K,hK,hC,⟨m⟩⟩ := s.local_lift_and_actionModel_of_whole_pair hi hne
  exact ⟨K,hK,hC,m,m.form_alternating s.hypothesis.alternating,
    m.form_nondegenerate s.hypothesis.nondegenerate,m.form_invariant B s.hypothesis.preserves⟩

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
