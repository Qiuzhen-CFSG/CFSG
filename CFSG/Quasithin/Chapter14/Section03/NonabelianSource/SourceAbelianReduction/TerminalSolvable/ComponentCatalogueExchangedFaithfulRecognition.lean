module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulSieveSourceRows
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulSieve
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.UnitarySource
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions.SourceModels
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.AtlasPort.LinearGroups.G2.Perfectness
/-!
# Recognition of the faithful exchanged component

The original exchanged constituent has degree m+2. The sharp two-component
bound has already made its faithful orbit image quasisimple. Exhausting the
actual simple and central-three-cover carriers now leaves only A7: each
other carrier contradicts the original actor rank, non-self-duality or proper
linear image. Every exclusion uses this same faithful H-action.

The final applications transport the recognized image back to the original
component and its local lift, including the original central-kernel branch.
The noncentral-kernel paired-A5 branch is separate.
Source: Aschbacher--Smith G.9.3 and G.11.6, printed pp.356 and 366.
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
open Chapter1.Section02 ClassificationModels
open ChapterG.Section09.DefiningCharacteristic.TwistedExclusions

private def image_center_quotient_equiv [IsSimpleGroup (s.image (componentOrbit L ⊤))] :
    (s.image (componentOrbit L ⊤)) ⧸ center (s.image (componentOrbit L ⊤)) ≃*
      s.image (componentOrbit L ⊤) := by
  let H := s.image (componentOrbit L ⊤)
  let : IsQuasisimple H := s.image_orbit_quasisimple
  have hz : center H = ⊥ := by
    rcases (inferInstance : (center H).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative H (center_eq_top_iff.mp ht)).elim
  exact (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot

private theorem image_alternating_seven_of_simple_model
    [IsSimpleGroup (s.image (componentOrbit L ⊤))]
    (hm : LocalModels.TheoremCModel (s.image (componentOrbit L ⊤))) :
    Nonempty (s.image (componentOrbit L ⊤) ≃* alternatingGroup (Fin 7)) := by
  let H := s.image (componentOrbit L ⊤)
  have h := s.image_single_component_hypothesis
  have q := s.image_center_quotient_equiv
  cases hm with
  | alternating n hn hm =>
    obtain ⟨e⟩ := hm
    obtain ⟨hnl,hnu⟩ := hn
    interval_cases n
    · exact (s.image_not_binary_rank_one (by decide : 2 ≤ 2)
        (by simpa only [Nat.card_eq_fintype_card] using GaloisField.card 2 2 (by decide))
        ((e.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm).trans
          (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 2)).symm)).elim
    · exact (s.image_not_alternating_six e).elim
    · exact ⟨e⟩
    · exact (s.image_not_binary_linear_four_or_five
        (Or.inl ⟨e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm⟩)).elim
  | linear_odd p e hp ho he _ hm =>
    exact (s.image_not_odd_linear_two hp ho (by rcases he with rfl | rfl <;> omega) hm).elim
  | three_odd p hp ho unitary hm =>
    apply False.elim
    apply s.image_not_odd_signed_three hp ho
    cases unitary
    · exact Or.inl hm
    · exact Or.inr (Or.inr (Or.inl hm))
  | rank_one hm =>
    apply False.elim
    cases hm with
    | linear n hn hm =>
      obtain ⟨K,_,_,hK,⟨e⟩⟩ := hm
      let : Fintype K := Fintype.ofFinite K
      let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
        (by simpa only [← Nat.card_eq_fintype_card] using hK)
      exact s.image_not_binary_rank_one hn hK (e.trans (Theory.PSL2.sl2QuotientEquiv K).symm)
    | unitary n hn hm =>
      obtain ⟨K,_,_,J,hK,hconj,he⟩ := hm
      exact not_unitary_three_positive_exponent h J (by omega) hK hconj (Or.inr he)
    | suzuki k hk he => exact s.image_not_suzuki hk he.some
  | rank_two hm =>
    apply False.elim
    cases hm with
    | linear n hn hm =>
      obtain ⟨K,_,_,hK,⟨e⟩⟩ := hm
      let : Fintype K := Fintype.ofFinite K
      let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
        (by simpa only [← Nat.card_eq_fintype_card] using hK)
      exact s.image_not_binary_linear_three_central_quotient hn hK (q.trans e)
    | symplectic n hn hm =>
      obtain ⟨K,_,_,hK,⟨e⟩⟩ := hm
      let : CharP K 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hK
      exact s.image_not_symplectic_four (by omega) hK
        ((e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm).trans
          (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hK hn).symm)
    | g2 n hn hm =>
      obtain ⟨K,_,_,hK,⟨e⟩⟩ := hm
      let : Fintype K := Fintype.ofFinite K
      let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
        (by simpa only [← Nat.card_eq_fintype_card] using hK)
      let : Group.IsPerfect (Atlas.G2.Model K) := Atlas.G2.isPerfect (by
        rw [hK]; exact (by norm_num : 2 = 2^1) ▸ Nat.pow_lt_pow_right (by decide) (by omega))
      let er : commutator (Atlas.G2.Model K) ≃* Atlas.G2.Model K :=
        (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv
      exact s.image_not_g2 (by omega) hK (e.trans er.symm)
    | triality n hn hm => exact not_triality_positive_exponent h hn hm
    | ree k hk hm =>
      obtain ⟨d,⟨e⟩⟩ := hm
      exact not_ree_of_local_block h hk d e
    | symplectic_derived he =>
      exact s.image_not_alternating_six
        (he.some.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
    | g2_derived he => exact s.image_not_g2_zmod_two he.some
    | tits he => exact not_tits_of_source_component h he.some
  | binary_linear n hn hm =>
    obtain ⟨K,_,_,hK,⟨e⟩⟩ := hm
    let : Fintype K := Fintype.ofFinite K
    let f : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hK)).symm
    have e' := e.trans (Atlas.fieldEquivPSL n f)
    apply False.elim
    apply s.image_not_binary_linear_four_or_five
    rcases hn with rfl | rfl
    · exact Or.inl ⟨e'⟩
    · exact Or.inr ⟨e'⟩
  | sporadic name hne he =>
    apply False.elim
    cases name with
    | m11 => exact h.not_m11_central_quotient (q.trans he.some)
    | m12 => exact s.image_not_mathieu (Or.inl he)
    | m22 => exact s.image_not_mathieu (Or.inr (Or.inl he))
    | m23 => exact s.image_not_mathieu (Or.inr (Or.inr (Or.inl he)))
    | m24 => exact s.image_not_mathieu (Or.inr (Or.inr (Or.inr he)))
    | j2 => exact s.image_not_remaining_sporadic (Or.inr (Or.inr (Or.inr (Or.inr he))))
    | j3 => exact hne rfl
    | j4 => exact s.image_not_remaining_sporadic (Or.inr (Or.inr (Or.inl he)))
    | hs => exact s.image_not_remaining_sporadic (Or.inl he)
    | he => exact s.image_not_remaining_sporadic (Or.inr (Or.inl he))
    | ru => exact s.image_not_remaining_sporadic (Or.inr (Or.inr (Or.inr (Or.inl he))))
  | janko_one he => exact (h.not_j1_central_quotient (q.trans he.some)).elim

private theorem image_not_three_cover_model
    (hm : LocalModels.ThreeCoverModel (s.image (componentOrbit L ⊤))) : False := by
  have h := s.image_single_component_hypothesis
  cases hm with
  | classical unitary q hq hm =>
    cases unitary
    · change LocalModels.IsSL _ 3 q at hm
      rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
      · obtain ⟨K,_,_,hK,⟨e⟩⟩ := hm
        let : Fintype K := Fintype.ofFinite K
        let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
          (by simpa only [← Nat.card_eq_fintype_card] using hK)
        exact s.image_not_binary_special_linear_three hn hK e
      · exact s.image_not_odd_signed_three hp ho (Or.inr (Or.inl hm))
    · change LocalModels.IsSU _ 3 q at hm
      rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hp,ho⟩
      · obtain ⟨K,_,_,J,hK,hconj,he⟩ := hm
        exact not_unitary_three_positive_exponent h J hn hK hconj (Or.inl he)
      · exact s.image_not_odd_signed_three hp ho (Or.inr (Or.inr (Or.inr hm)))
  | alternating_six hm =>
    exact s.image_not_triple_alternating_six_central_quotient hm.2.2.some
      ((Nat.card_congr hm.2.1.some.toEquiv).trans (by simp))
  | alternating_seven hm =>
    exact s.image_not_triple_alternating_seven hm.2.2.some
      ((Nat.card_congr hm.2.1.some.toEquiv).trans (by simp))
  | mathieu hm => exact s.image_not_m22_central_quotient hm.2.2.some

theorem image_alternating_seven :
    Nonempty (s.image (componentOrbit L ⊤) ≃* alternatingGroup (Fin 7)) := by
  rcases s.image_orbit_models with ⟨hs,hm⟩ | ⟨_,hm⟩
  · let := hs
    exact s.image_alternating_seven_of_simple_model hm
  · exact (s.image_not_three_cover_model hm).elim

/-- The original component catalogue, with no action-recognition premise. -/
theorem component_image_cases : ComponentImageCases L :=
  s.componentImageCases_of_image_alternating_seven s.image_alternating_seven.some

/-- The literal terminal lift of the recognized original component. -/
theorem local_lift :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_alternating_seven s.image_alternating_seven.some

end ExchangedFaithfulSource

namespace ExchangedCentralSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedCentralSource T M Mc F g B v L I)

include s

/-- Original central-kernel source data give the original component cases. -/
theorem component_image_cases : ComponentImageCases L :=
  ExchangedFaithfulSource.component_image_cases s.faithful_source

/-- Original central-kernel source data give the actual ambient local lift. -/
theorem local_lift :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  ExchangedFaithfulSource.local_lift s.faithful_source

end ExchangedCentralSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
