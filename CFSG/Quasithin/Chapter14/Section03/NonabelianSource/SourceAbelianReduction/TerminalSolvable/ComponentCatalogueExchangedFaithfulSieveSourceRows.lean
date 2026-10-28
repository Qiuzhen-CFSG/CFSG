module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulSingleComponent
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulSieveDefiningCharacteristic
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic
public import CFSG.Quasithin.ChapterG.Section07.AlternatingSevenCover
public import Theory.SpecificGroups.PSL3.OddDegreeProjectiveComparison
public import Theory.Representation.Suzuki.BinaryDegree
public import CFSG.Quasithin.ChapterG.Section09.SingleComponentExclusions
/-!
# Remaining odd-characteristic carrier reductions in the exchanged branch

The actual odd PSL2 and signed ternary actions satisfy the completed G.7
recognition bounds, so they reduce to binary models already excluded on this
same orbit image. Suzuki and triple A7 are excluded directly by their actual
degree and automorphism bounds. The last theorem applies the shared source
exclusions to the literal exchanged image and its actual G.9 hypothesis.
Source: Aschbacher--Smith G.7.3, G.9.3 and G.11.6, pp.348,356,366.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
namespace ExchangedFaithfulSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedFaithfulSource T M Mc F g B v L I)

include s


open scoped MatrixGroups
open ChapterG.Section07

/-- The source odd PSL2 alternatives reduce to the already excluded actual
binary rank-one, linear-three and alternating-six images. -/
theorem image_not_odd_linear_two {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (hm : ClassicalGroup.IsPSL (s.image (componentOrbit L ⊤)) 2 (p ^ e)) : False := by
  let H := s.image (componentOrbit L ⊤)
  let : IsQuasisimple H := s.image_orbit_quasisimple
  have hd := s.image_degree_le_automorphism_rank_add_two
  rcases OddCharacteristic.psl2_identification_of_degree_le_automorphism_rank
    (s.imageAction.comp H.subtype) (s.image_setup.faithful.comp H.subtype_injective)
    hp ho he hm (by dsimp [H]; omega) with hb | ht | hs
  · obtain ⟨K,_,_,hK,⟨f⟩⟩ := hb
    let : Fintype K := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by simpa only [← Nat.card_eq_fintype_card, Nat.reducePow] using hK)
    exact s.image_not_binary_rank_one (by decide : 2 ≤ 2)
      (by simpa only [Nat.reducePow] using hK) (f.trans (Theory.PSL2.sl2QuotientEquiv K).symm)
  · obtain ⟨K,_,_,hK,⟨f⟩⟩ := ht
    let : Fintype K := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by simpa only [← Nat.card_eq_fintype_card, pow_one] using hK)
    have hz := Matrix.PSL3.OddDegreeProjectiveComparison.center_eq_bot (F := K)
      (n := 1) (by simpa using hK) (by decide)
    let eq : PSL(3,K) ≃* SL(3,K) :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
    exact s.image_not_binary_special_linear_three (by decide : 0 < 1)
      (by simpa using hK) (f.trans eq)
  · exact s.image_not_binary_symplectic_four (by simp) (Classical.choice hs)

/-- Odd signed ternary carriers reduce to the genuine binary derived G2. -/
theorem image_not_odd_signed_three {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : OddCharacteristic.IsLinearUnitaryThree (s.image (componentOrbit L ⊤)) p) : False := by
  let H := s.image (componentOrbit L ⊤)
  let : IsQuasisimple H := s.image_orbit_quasisimple
  let : IsIrreducible (s.imageAction.comp H.subtype) := s.image_irreducible
  have hd := s.image_degree_le_automorphism_rank_add_two
  obtain ⟨⟨e⟩,_⟩ := OddCharacteristic.linear_unitary_three_of_degree_le_automorphism_rank
    (s.imageAction.comp H.subtype) (s.image_setup.faithful.comp H.subtype_injective)
    hp ho hm (by dsimp [H]; omega)
  exact s.image_not_g2_zmod_two e

/-- Suzuki's faithful binary minimum exceeds the sharp original degree. -/
theorem image_not_suzuki {k : ℕ} (hk : 1 ≤ k)
    (e : s.image (componentOrbit L ⊤) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup k) : False := by
  let H := s.image (componentOrbit L ⊤)
  let σ := (s.imageAction.comp H.subtype).comp e.symm.toMonoidHom
  have hf : Function.Injective σ :=
    s.image_setup.faithful.comp (H.subtype_injective.comp e.symm.injective)
  have hl := Representation.Suzuki.finrank_ge hk σ hf
  have hu := s.image_degree_le_automorphism_rank_add_two
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := BenderSuzuki.MatrixGroups.suzuki_automorphism_two_rank k hk
  omega

/-- The actual triple cover of A7 has degree divisible by six, but the sharp
actor bound permits degree at most five. -/
theorem image_not_triple_alternating_seven
    (e : s.image (componentOrbit L ⊤) ⧸ center (s.image (componentOrbit L ⊤)) ≃*
      alternatingGroup (Fin 7))
    (hz : Nat.card (center (s.image (componentOrbit L ⊤))) = 3) : False := by
  let H := s.image (componentOrbit L ⊤)
  let : IsQuasisimple H := s.image_orbit_quasisimple
  let : IsIrreducible (s.imageAction.comp H.subtype) := s.image_irreducible
  have hr := AlternatingSevenCover.cover_automorphism_two_rank e
  have hl := AlternatingSevenCover.six_dvd_dimension e hz
    (s.imageAction.comp H.subtype) (s.image_setup.faithful.comp H.subtype_injective)
  have hu := s.image_degree_le_automorphism_rank_add_two
  have hp := s.dimension_gt_two
  omega

/-- The original same-H G.9 input with both component positions identified. -/
theorem image_single_component_hypothesis :
    ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple s.imageAction
      (s.image (actor (F := F) (g := g) (I := I)))
      (s.image (componentOrbit L ⊤)) (s.image (componentOrbit L ⊤))
      (finrank (ZMod 2) I - 2) := by
  have hc := s.componentInput
  change ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple s.imageAction
    (s.image (actor (F := F) (g := g) (I := I))) (s.image L)
    (s.image (componentOrbit L ⊤)) (finrank (ZMod 2) I - 2) at hc
  simpa only [s.orbit_eq_component] using hc

/-- The actual source simple sporadic rows are excluded using the original
action and sharp actor bound, without a universal classification callback. -/
theorem image_not_remaining_sporadic [IsSimpleGroup (s.image (componentOrbit L ⊤))] :
    ¬ (Nonempty (s.image (componentOrbit L ⊤) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty (s.image (componentOrbit L ⊤) ≃* Held.He) ∨
      Nonempty (s.image (componentOrbit L ⊤) ≃* Janko4.Model) ∨
      Nonempty (s.image (componentOrbit L ⊤) ≃* Rudvalis.Model) ∨
      Nonempty (s.image (componentOrbit L ⊤) ≃* Sporadic.LeechRelated.J2.Carrier)) := by
  intro hm
  have h := s.image_single_component_hypothesis
  rcases hm with hm | hm | hm | hm | hm
  · exact h.not_higman_sims hm.some
  · exact h.not_held hm.some
  · exact h.not_janko_four hm.some
  · exact h.not_rudvalis hm.some
  · apply h.not_janko_two_of_sharp_degree ?_ hm.some
    have := s.dimension_gt_two
    omega

end ExchangedFaithfulSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
