module

public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.GroupAction.InnerInvolutionGeometry
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCentralizerNineFree
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M23.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.SylowCatalogue.Enumeration
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.Core
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.SpecificGroups.Held.TwoPartDivisibility

/-!
# The marked component list with two-part at most sixty-four

Concrete unipotent subgroup orders bound the field parameters in every
characteristic-two row of 1.1.5. When 128 does not divide the group order,
eight small Lie alternatives remain. The same bound on the intrinsic
two-core quotient excludes the G₂(4) cover and all allowed sporadic carriers
except M₁₁ and M₁₂. The J₄ and HS exclusions need only their existing local
two-subgroups, of orders 2¹³ and 2⁹.

The reduced action list retains the original automorphism, the genuine
model equivalences, the L₃(4) central-cover row, both alternating actions
including their triple covers, and the odd rows. This is a numerical
reduction of the catalogue, not a recognition of an ambient extension.
The literal opposite-centralizer application is in Chapter14's
`OppositeCentralizer.RecognitionModelSieve`.

Source: Aschbacher--Smith 1.1.5(3), printed pp.501--503, and the model
inspection in 14.3.22, printed p.999; refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ClassificationModels CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
namespace CFSG.Quasithin.Chapter1.SmallTwoPart
variable {X : Type*} [Group X]

/-- The characteristic-two rows whose two-part is at most sixty-four. -/
def LieModels (X : Type*) [Group X] : Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ f ≤ 6 ∧ ClassicalGroup.IsPSL X 2 (2 ^ f)) ∨
  ClassicalGroup.IsPSU X 3 4 ∨
  Nonempty (X ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1) ∨
  ClassicalGroup.IsPSL X 3 2 ∨ ClassicalGroup.IsPSL X 3 4 ∨
  Nonempty (X ≃* alternatingGroup (Fin 6)) ∨
  Nonempty (X ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
  ClassicalGroup.IsPSL X 4 2

private theorem power_dvd {a b : ℕ} (h : 7 ≤ a * b) : 128 ∣ (2 ^ a) ^ b := by
  rw [← pow_mul]
  exact Nat.pow_dvd_pow 2 h

omit [Group X] in
private theorem parameter_le_two {f : ℕ} (h : ¬128 ∣ Nat.card X)
    (hd : (2 ^ f) ^ 3 ∣ Nat.card X) : f ≤ 2 := by
  by_contra hn
  exact h ((power_dvd (by omega)).trans hd)

private theorem rankOne (hm : IsBenderModel X) (hsmall : ¬128 ∣ Nat.card X) :
    LieModels X := by
  classical
  cases hm with
  | linear f hf iso =>
    refine Or.inl ⟨f, hf, ?_, iso⟩
    obtain ⟨F, hFfield, hFfinite, hF, ⟨e⟩⟩ := iso
    let := hFfield
    let := hFfinite
    let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hd := (BenderSuzuki.Converse.PUnip F).card_subgroup_dvd_card
    rw [BenderSuzuki.Converse.PUnip_card, hF, ←Nat.card_congr e.toEquiv] at hd
    by_contra hn
    exact hsmall ((Nat.pow_dvd_pow 2 (show 7 ≤ f by omega)).trans hd)
  | unitary f hf iso =>
    have hf2 : f = 2 := by
      obtain ⟨F, hFfield, hFfinite, J, hF, hconj, ⟨e⟩⟩ := iso
      let := hFfield
      let := hFfinite
      have hd := BenderSuzuki.MatrixGroups.HermitianForm.BinarySylowOrder.cube_dvd_card_projective
        J (by omega : f ≠ 0) hF hconj
      rw [←Nat.card_congr e.toEquiv] at hd
      have := parameter_le_two hsmall hd
      omega
    subst f
    exact Or.inr (Or.inl iso)
  | suzuki m hm iso =>
    have hm1 : m = 1 := by
      obtain ⟨e⟩ := iso
      have hd : (2 ^ (2*m+1)) ^ 2 ∣ Nat.card X := by
        rw [Nat.card_congr e.toEquiv, BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m (by omega)]
        exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
      by_contra hn
      exact hsmall ((power_dvd (by omega)).trans hd)
    subst m
    exact Or.inr (Or.inr (Or.inl iso))

private theorem rankTwo (hm : RankTwoTheoremC X) (hsmall : ¬128 ∣ Nat.card X) :
    LieModels X := by
  classical
  cases hm with
  | linear f hf iso =>
    have hf2 : f ≤ 2 := by
      obtain ⟨F, hFfield, hFfinite, hF, ⟨e⟩⟩ := iso
      let := hFfield
      let := hFfinite
      have hd := (Matrix.PSL3.LinearThree.unipotent F).card_subgroup_dvd_card
      rw [Matrix.PSL3.LinearThree.card_unipotent, hF, ←Nat.card_congr e.toEquiv] at hd
      exact parameter_le_two hsmall hd
    have hf' : f = 1 ∨ f = 2 := by omega
    rcases hf' with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl iso)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl iso))))
  | symplectic f hf iso =>
    obtain ⟨F, hFfield, hFfinite, hF, ⟨e⟩⟩ := iso
    let := hFfield
    let := hFfinite
    let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let b := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
    have hd := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F)).card_subgroup_dvd_card
    rw [Theory.SpecificGroups.SymplecticFour.card_unipotent, hF,
      ←Nat.card_congr b.toEquiv] at hd
    exact (hsmall ((power_dvd (by omega)).trans hd)).elim
  | g2 f hf iso =>
    obtain ⟨F, hFfield, hFfinite, hF, ⟨e⟩⟩ := iso
    let := hFfield
    let := hFfinite
    have hd : (2 ^ f) ^ 6 ∣ Nat.card X := by
      rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model, hF]
      exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
    exact (hsmall ((power_dvd (by omega)).trans hd)).elim
  | triality f hf iso =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff X f (by omega)).mp iso
    have hd := (Triality.Standard.Parabolics.unipotent
      (Triality.Standard.binaryParameters f (by omega))).card_subgroup_dvd_card
    rw [Triality.Standard.Parabolics.card_unipotent_binary _ rfl] at hd
    change (2 ^ f) ^ 12 ∣ Nat.card (Triality.Standard.BinaryCarrier f _) at hd
    rw [←Nat.card_congr e.toEquiv] at hd
    exact (hsmall ((power_dvd (by omega)).trans hd)).elim
  | ree m hm iso =>
    obtain ⟨d, ⟨e⟩⟩ := iso
    let b := e.trans d.modelEquiv
    have hd := (ReeF4.Parabolics.unipotent m).card_subgroup_dvd_card
    rw [ReeF4.Parabolics.card_unipotent, ←Nat.card_congr b.toEquiv] at hd
    exact (hsmall ((power_dvd (by omega)).trans hd)).elim
  | symplectic_derived iso =>
    obtain ⟨e⟩ := iso
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩)))))
  | g2_derived iso =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl iso))))))
  | tits iso =>
    obtain ⟨e⟩ := iso
    have ho : Nat.card X = 17971200 :=
      (Nat.card_congr e.toEquiv).trans Tits.parrottGroup_card
    exact (hsmall (ho ▸ (by decide : 128 ∣ 17971200))).elim

/-- Numerical inspection of every characteristic-two row, including the small derived groups. -/
theorem lieModels_of_not_dvd (hm : LieTypeTwoModel X) (hsmall : ¬128 ∣ Nat.card X) :
    LieModels X := by
  classical
  rcases hm with hm | hm | ⟨n, hn, hm⟩
  · exact rankOne hm hsmall
  · exact rankTwo hm hsmall
  · rcases hn with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hm))))))
    · obtain ⟨F, hFfield, hFfinite, hF, ⟨e⟩⟩ := hm
      let := hFfield
      let := hFfinite
      have ho := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
      rw [hF] at ho
      norm_num [Fin.prod_univ_succ] at ho
      have hh : Nat.card X = 9999360 := (Nat.card_congr e.toEquiv).trans ho
      exact (hsmall (hh ▸ (by decide : 128 ∣ 9999360))).elim

/-- All allowed sporadic carriers except M₁₁ and M₁₂ have two-part at least 128. -/
theorem sporadic_name_of_not_dvd (name : SporadicName) (hne : name ≠ .j3)
    (hsmall : ¬128 ∣ Nat.card name.Carrier) : name = .m11 ∨ name = .m12 := by
  cases name with
  | m11 => exact Or.inl rfl
  | m12 => exact Or.inr rfl
  | m22 => exact (hsmall (Sporadic.Mathieu.m22_order ▸ (by decide : 128 ∣ 443520))).elim
  | m23 => exact (hsmall (Sporadic.Mathieu.m23_order ▸ (by decide : 128 ∣ 10200960))).elim
  | m24 => exact (hsmall (Sporadic.Mathieu.m24_order ▸ (by decide : 128 ∣ 244823040))).elim
  | j2 => exact (hsmall (Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier ▸
      (by decide : 128 ∣ 604800))).elim
  | j3 => exact (hne rfl).elim
  | j4 =>
    have hd := (pCore 2 Janko4.InvolutionCentralizers.First.centralizer).card_subgroup_dvd_card.trans
      Janko4.InvolutionCentralizers.First.centralizer.card_subgroup_dvd_card
    rw [Janko4.InvolutionCentralizers.First.centralizer_twoCore_card] at hd
    exact (hsmall ((by decide : 128 ∣ 2^13).trans hd)).elim
  | hs =>
    have hd := Sporadic.LeechRelated.HS.EvenLocalCandidates.subgroup.card_subgroup_dvd_card
    rw [Sporadic.LeechRelated.HS.EvenLocalCandidates.SylowCatalogueData.subgroup_card] at hd
    exact (hsmall ((by decide : 128 ∣ 2^9).trans hd)).elim
  | he => exact (hsmall ((by decide : 128 ∣ 2^10).trans Held.two_pow_ten_dvd_card)).elim
  | ru => exact (hsmall (Rudvalis.model_card ▸ (by decide : 128 ∣ 145926144000))).elim

/-- The full action list after the two-part bound. The remaining central cover
is still a cover, and the alternating and odd actions keep all their markings. -/
inductive SmallModelAction115 (X : Type*) [Group X] (α : MulAut X) : Prop
  | lie (simple : IsSimpleGroup X) (model : LieModels X)
      (inner : α ∈ (MulAut.conj (G := X)).range)
  | two_cover (nontrivial_center : center X ≠ ⊥) (center_eq : center X = pCore 2 X)
      (model : ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 3 4)
      (inner : α ∈ (MulAut.conj (G := X)).range)
  | six (σ : Equiv.Perm (Fin 6)) (transposition : σ.IsSwap)
      (action : AlternatingAction α 6 σ)
  | seven (σ : Equiv.Perm (Fin 7)) (cycles : σ.cycleType = {2, 2, 2})
      (action : AlternatingAction α 7 σ)
  | odd (model : ClassicalGroup.IsPSL X 3 3 ∨
        ∃ p : ℕ, CFSG.Quasithin.IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL X 2 p)
      (inner : α ∈ (MulAut.conj (G := X)).range)
  | sporadic (name : SporadicName) (small : name = .m11 ∨ name = .m12)
      (model : Nonempty ((X ⧸ pCore 2 X) ≃* name.Carrier))
      (action : TwoCentralInner α)

/-- The two-part bound narrows every case of the genuine catalogue while
retaining the original automorphism and actual model equivalences. -/
theorem smallModelAction115_of_not_dvd [Finite X] [IsQuasisimple X] {α : MulAut X}
    (hm : ModelAction115 X α) (hsmall : ¬128 ∣ Nat.card (X ⧸ pCore 2 X)) :
    SmallModelAction115 X α := by
  cases hm with
  | lie hs hm hi =>
    let := hs
    have hz : center X = ⊥ := center_eq_bot_of_simple_perfect
    have hp : pCore 2 X = ⊥ := bot_unique (hz ▸ IsQuasisimple.pCore_le_center 2)
    have hsmallX : ¬128 ∣ Nat.card X := by
      rwa [hp, Nat.card_congr (QuotientGroup.quotientBot (G := X)).toEquiv] at hsmall
    exact .lie hs (lieModels_of_not_dvd hm hsmallX) hi
  | two_cover hn hz hm hi =>
    apply SmallModelAction115.two_cover hn hz _ hi
    rcases hm with hm | hm
    · exact hm
    · obtain ⟨F, hFfield, hFfinite, hF, ⟨e⟩⟩ := hm
      let := hFfield
      let := hFfinite
      have hd : 4 ^ 6 ∣ Nat.card (X ⧸ pCore 2 X) := by
        rw [Nat.card_congr e.toEquiv, Atlas.G2.card_Model, hF]
        exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
      exact (hsmall ((by decide : 128 ∣ 4^6).trans hd)).elim
  | six σ ht ha => exact .six σ ht ha
  | seven σ ht ha => exact .seven σ ht ha
  | odd hm hi => exact .odd hm hi
  | sporadic name hn hm ha =>
    have hs : name = .m11 ∨ name = .m12 := sporadic_name_of_not_dvd name hn (by
      rwa [←Nat.card_congr hm.some.toEquiv])
    exact .sporadic name hs hm ha

end CFSG.Quasithin.Chapter1.SmallTwoPart
