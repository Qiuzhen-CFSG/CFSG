module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedModelTransports
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedUnitary
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedTwisted
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedSharpExclusions
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentModels
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentExclusions
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Complete marked two-copy image recognition

The sharp original actor bound makes the normal component orbit one actual
component. The completed single-component carrier catalogue then leaves only
the permitted A5, A6, A7 and binary derived G2 rows. Binary classical model
predicates are transported through the literal covering and quotient maps;
the remaining actual models are excluded by their proved degree and actor
bounds. The A8 row uses the original doubled action and ambient exclusion.
Every large output retains equality with the normal component orbit.

This closes the two-copy branch without a classification callback. The final
marked image theorem still needs faithful-actor recognition.
Source: Aschbacher–Smith G.11.8 and 14.3.15, printed pp.368–369,994.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
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

open scoped MatrixGroups
open Chapter1.Section02.LocalModels

local notation "C" => MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
  (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L
local notation "Xᵢ" => MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
  (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes (F.terminalDot (F.X g))
local notation "ρᵢ" => kerRepresentation (MarkedAction.action F.terminalRepresentation
  (componentOrbit L ⊤) (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes)

private theorem two_copy_input
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I) :
    ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρᵢ Xᵢ C C
      (Module.finrank (ZMod 2) I - 2) := by
  have hHL := s.orbit_eq_component_of_double_dimension hk hd
  have he := congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
  have hc := s.componentHypothesis_of_double_dimension hk hd
  dsimp only at hc
  rwa [he] at hc

private theorem imageCases_of_double_dimension_odd_two
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (hm : ClassicalGroup.IsPSL C 2 (p ^ e)) : s.ImageCases := by
  have hc := s.two_copy_input hk hd
  let : IsQuasisimple C := hc.component.2
  rcases ChapterG.Section07.OddCharacteristic.psl2_identification_of_degree_le_automorphism_rank
    ((ρᵢ).comp (C).subtype) (hc.faithful.comp (C).subtype_injective)
    hp ho he hm hc.single_component_degree_bound with hb | ht | hs
  · apply s.imageCases_of_double_dimension_projective_rank_one hk hd (n := 2) (by decide)
    simpa using hb
  · exact (s.not_double_dimension_projective_linear_three hk hd (n := 1) (by decide)
      (by simpa using ht)).elim
  · exact s.imageCases_of_double_dimension_symplectic hk hd hs.some 1 (by decide) (by simp)

private theorem imageCases_of_double_dimension_odd_three
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ChapterG.Section07.OddCharacteristic.IsLinearUnitaryThree C p) : s.ImageCases := by
  have hc := s.two_copy_input hk hd
  let : IsQuasisimple C := hc.component.2
  let : IsIrreducible ((ρᵢ).comp (C).subtype) := hc.irreducible
  obtain ⟨e,_⟩ := ChapterG.Section07.OddCharacteristic.linear_unitary_three_of_degree_le_automorphism_rank
    ((ρᵢ).comp (C).subtype) (hc.faithful.comp (C).subtype_injective)
    hp ho hm hc.single_component_degree_bound
  exact s.imageCases_of_double_dimension_g2 hk hd e.some 1 (by decide) (by simp)

private theorem imageCases_of_double_dimension_alternating_group
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    {n : ℕ} (hn : 5 ≤ n ∧ n ≤ 8) (e : C ≃* alternatingGroup (Fin n)) : s.ImageCases := by
  obtain ⟨hnl,hnu⟩ := hn
  interval_cases n
  · exact Or.inr (Or.inl (Or.inl ⟨e⟩))
  · exact Or.inr (Or.inl (Or.inr ⟨e⟩))
  · have hHL := s.orbit_eq_component_of_double_dimension hk hd
    exact Or.inl ⟨congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL,
      Or.inr (Or.inl ⟨e⟩)⟩
  · exact s.imageCases_of_double_dimension_binary_four hk hd
      (e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two)

private theorem imageCases_of_double_dimension_rank_one_models
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (hm : ClassificationModels.IsBenderModel C) : s.ImageCases := by
  cases hm with
  | linear n hn hm => exact s.imageCases_of_double_dimension_projective_rank_one hk hd hn hm
  | unitary n hn hm =>
    obtain ⟨k,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
    exact (s.not_double_dimension_unitary_three hk hd J n (by omega) hcard hconj
      (Or.inr ⟨e⟩)).elim
  | suzuki k hk' e => exact ((s.two_copy_input hk hd).not_suzuki hk' e.some).elim

private theorem imageCases_of_double_dimension_rank_two_models
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (hm : RankTwoTheoremC C) : s.ImageCases := by
  cases hm with
  | linear n hn hm => exact (s.not_double_dimension_projective_linear_three hk hd (by omega) hm).elim
  | symplectic n hn hm => exact s.imageCases_of_double_dimension_projective_symplectic hk hd hn hm
  | g2 n hn hm => exact s.imageCases_of_double_dimension_full_g2 hk hd hn hm
  | triality n hn hm =>
    exact (s.not_double_dimension_triality_ree_tits hk hd (Or.inl ⟨n,by omega,hm⟩)).elim
  | ree k hk' hm =>
    exact (s.not_double_dimension_triality_ree_tits hk hd (Or.inr (Or.inl ⟨k,hk',hm⟩))).elim
  | symplectic_derived e => exact s.imageCases_of_double_dimension_projective_symplectic_derived hk hd e.some
  | g2_derived e => exact s.imageCases_of_double_dimension_g2 hk hd e.some 1 (by decide) (by simp)
  | tits e => exact (s.not_double_dimension_triality_ree_tits hk hd (Or.inr (Or.inr e))).elim

omit s in
private theorem simple_center_eq_bot {D : Type*} [Group D] [IsSimpleGroup D]
    [Group.IsPerfect D] : center D = ⊥ := by
  rcases (inferInstance : (center D).Normal).eq_bot_or_eq_top with he | he
  · exact he
  · exact (Group.IsPerfect.not_isMulCommutative D (center_eq_top_iff.mp he)).elim

private theorem imageCases_of_double_dimension_simple_models
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (hs : IsSimpleGroup C) (hm : TheoremCModel C) : s.ImageCases := by
  have hc := s.two_copy_input hk hd
  let : IsSimpleGroup C := hs
  let : IsQuasisimple C := hc.component.2
  let eZ : (C ⧸ center C) ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq simple_center_eq_bot).trans QuotientGroup.quotientBot
  have hsharp : Module.finrank (ZMod 2) I ≤ Module.finrank (ZMod 2) I - 2 + 2 := by
    have := s.dimension_gt_two
    omega
  cases hm with
  | alternating n hn e => exact s.imageCases_of_double_dimension_alternating_group hk hd hn e.some
  | linear_odd p e hp ho he _ hm =>
    exact s.imageCases_of_double_dimension_odd_two hk hd hp ho (by rcases he with rfl | rfl <;> decide) hm
  | three_odd p hp ho u hm =>
    apply s.imageCases_of_double_dimension_odd_three hk hd hp ho
    cases u with
    | false => exact Or.inl hm
    | true => exact Or.inr (Or.inr (Or.inl hm))
  | rank_one hm => exact s.imageCases_of_double_dimension_rank_one_models hk hd hm
  | rank_two hm => exact s.imageCases_of_double_dimension_rank_two_models hk hd hm
  | binary_linear n hn hm => exact s.imageCases_of_double_dimension_binary_linear_model hk hd hn hm
  | sporadic name hne e =>
    cases name with
    | m11 => exact (hc.not_m11_central_quotient (eZ.trans e.some)).elim
    | m12 => exact (hc.not_m12_of_sharp_degree hsharp e.some).elim
    | m22 => exact (hc.not_m22_of_sharp_degree hsharp e.some).elim
    | m23 => exact (hc.not_m23_of_sharp_degree hsharp e.some).elim
    | m24 => exact (hc.not_m24_of_sharp_degree hsharp e.some).elim
    | j2 => exact (hc.not_janko_two_of_sharp_degree hsharp e.some).elim
    | j3 => exact (hne rfl).elim
    | j4 => exact (hc.not_janko_four e.some).elim
    | hs => exact (hc.not_higman_sims e.some).elim
    | he => exact (hc.not_held e.some).elim
    | ru => exact (hc.not_rudvalis e.some).elim
  | janko_one e => exact (hc.not_j1_central_quotient (eZ.trans e.some)).elim

private theorem imageCases_of_double_dimension_cover_models
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (hm : ThreeCoverModel C) : s.ImageCases := by
  have hc := s.two_copy_input hk hd
  have hsharp : Module.finrank (ZMod 2) I ≤ Module.finrank (ZMod 2) I - 2 + 2 := by
    have := s.dimension_gt_two
    omega
  cases hm with
  | classical u q hq hm =>
    rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
    · cases u with
      | false => exact (s.not_double_dimension_special_linear_three hk hd (by omega) hm).elim
      | true =>
        obtain ⟨k,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
        exact (s.not_double_dimension_unitary_three hk hd J n (by omega) hcard hconj (Or.inl ⟨e⟩)).elim
    · apply s.imageCases_of_double_dimension_odd_three hk hd hp ho
      cases u with
      | false => exact Or.inr (Or.inl hm)
      | true => exact Or.inr (Or.inr (Or.inr hm))
  | alternating_six hm =>
    exact (hc.not_triple_alternating_six_of_sharp_degree hsharp hm.2.2.some
      ((Nat.card_congr hm.2.1.some.toEquiv).trans (by simp))).elim
  | alternating_seven hm =>
    exact (hc.not_triple_alternating_seven hm.2.2.some
      ((Nat.card_congr hm.2.1.some.toEquiv).trans (by simp))).elim
  | mathieu hm => exact (hc.not_m22_central_quotient_of_sharp_degree hsharp hm.2.2.some).elim

/-- The complete two-copy constituent classifier uses the exhaustive original
single-component catalogue and retains the actual image orbit in large rows. -/
theorem imageCases_of_double_dimension_complete
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I) : s.ImageCases := by
  rcases (s.two_copy_input hk hd).single_component_models with ⟨hs,hm⟩ | ⟨_,hm⟩
  · exact s.imageCases_of_double_dimension_simple_models hk hd hs hm
  · exact s.imageCases_of_double_dimension_cover_models hk hd hm

/-- The completed two-copy branch gives the original intrinsic component lift. -/
theorem local_lift_of_double_dimension_complete
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases (s.imageCases_of_double_dimension_complete hk hd)
end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
