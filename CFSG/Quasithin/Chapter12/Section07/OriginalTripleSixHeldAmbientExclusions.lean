module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldFullAffine
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality
public import Theory.Mathieu.M24.Properties.InvolutionFixedOrders
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
The original affine normalizer excludes the degree-five binary linear group.
The original escaping point component has a PSL₃(4) quotient, so nine divides
its centralizer order. Native M₂₄ involution coverage and the two certified
centralizer calculations exclude M₂₄ from this same original configuration.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open Theory.GroupTheory.CentralizerSmallKernelTransport
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem centralizer_card_of_conjugate {X : Type*} [Group X]
    {x y : X} (hxy : IsConj x y) :
    Nat.card (centralizer ({x} : Set X)) = Nat.card (centralizer ({y} : Set X)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  have he : (MulAut.conj g) x = y := hg
  rw [Nat.card_congr (centralizerEquiv (MulAut.conj g) x).toEquiv, he]

private theorem m24_centralizer_not_nine (x : Sporadic.Mathieu.M24)
    (hx : orderOf x = 2) : ¬ 9 ∣ Nat.card (centralizer ({x} : Set Sporadic.Mathieu.M24)) := by
  open Sporadic.Mathieu.M24InvolutionCentralizers in
  rcases involution_classes x hx with h | h
  · rw [← centralizer_card_of_conjugate h,
      Sporadic.Mathieu.M24InvolutionCentralizers.TwoA.centralizer_card]
    decide
  · rw [← centralizer_card_of_conjugate h]
    exact Sporadic.Mathieu.M24InvolutionFixedOrders.centralizer_twoB_not_nine

/-- The two non-Held simple alternatives are excluded using the unchanged
original normalizer and point centralizer. The divisibility witnesses are
included for downstream recognition without any model-shape hypotheses. -/
theorem original_tripleSix_escaping_ambient_exclusions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    138240 ∣ Nat.card G ∧
      9 ∣ Nat.card (centralizer ({(t : G)} : Set G)) ∧
      ¬ Nonempty (G ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∧
      ¬ Nonempty (G ≃* PSL(5, ZMod 2)) ∧
      ¬ Nonempty (G ≃* Sporadic.Mathieu.M24) := by
  let M := normalizer (K : Set G)
  obtain ⟨_, Y, _, _, E, _, _, _⟩ :=
    original_tripleSix_escaping_full_affine_model h structural D a t ht heven hout
  have hMc : Nat.card M = 138240 := by
    rw [Nat.card_congr E.toEquiv, SemidirectProduct.card,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative hexacode ≃ hexacode),
      hexacode_card, hexAutomorphisms_card]
  have hMG : 138240 ∣ Nat.card G := hMc ▸ M.card_subgroup_dvd_card
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  let Vt := tripleSixPoint D a t
  obtain ⟨_, _, _, hn, ⟨e⟩⟩ :=
    original_tripleSix_point_identification_at h structural D a t ht heven hout
  let := hn
  have hquot : Nat.card (B ⧸ Vt.subgroupOf B) = 20160 :=
    (Nat.card_congr e.toEquiv).trans Matrix.PSL3Four.card_PSL
  have hBH : B ≤ H := conjugateSpanBy_le_self (map_subtype_le _ |>.trans inf_le_right)
  have hHC : 9 ∣ Nat.card H :=
    (by decide : 9 ∣ 20160).trans
      ((hquot ▸ (Vt.subgroupOf B).card_quotient_dvd_card).trans (card_dvd_of_le hBH))
  have hSL : ¬ Nonempty (G ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := by
    rintro ⟨f⟩
    have hc : Nat.card G = 9999360 := by
      rw [Nat.card_congr f.toEquiv, BinaryLinear.card_SL]
      decide +kernel
    rw [hc] at hMG
    exact (by decide : ¬ 138240 ∣ 9999360) hMG
  refine ⟨hMG, hHC, hSL, ?_, ?_⟩
  · rintro ⟨f⟩
    exact hSL ⟨f.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide))⟩
  · rintro ⟨f⟩
    let := D.elementary
    have ht2 : orderOf (t : G) = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (t : G) t.property)
      (fun he => ht (Subtype.ext he))
    have hf : orderOf (f (t : G)) = 2 := (f.orderOf_eq _).trans ht2
    exact m24_centralizer_not_nine _ hf
      ((Nat.card_congr (centralizerEquiv f (t : G)).toEquiv) ▸ hHC)

end CFSG.Quasithin.Chapter12.Section07
