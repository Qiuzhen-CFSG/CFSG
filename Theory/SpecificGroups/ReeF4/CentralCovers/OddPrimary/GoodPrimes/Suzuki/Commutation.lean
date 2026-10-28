module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.PairIndex.Swap.Standard
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.EqualLength

/-!
# Commuting orthogonal B₂ planes in characteristic two

Positive orthogonal roots either have no root sum, or are short with a long
sum. In the latter case the Chevalley coefficient is two, hence zero in the
Ree coefficient field. Two Weyl words independently negate the two coordinate
planes; conjugating by them removes the positivity restriction. Closure then
proves commutation of the two entire signed B₂ Levis and their fixed subgroups.

Source: GLS3, Example 2.6.3, `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.CentralCovers.OddPrimary.SuzukiOrthogonal
open Subgroup Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open LocalBlockInput.PairRigidity LocalBlockInput.PairRigidity.FixedCollection
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open MaximalSubgroups.CommutingComponents.CarrierIdentification
open MaximalSubgroups.CommutingComponents.PairSwap
open Parabolics.RadicalCoordinates Parabolics.Binary.FixedGeometry LargeLocalSeeds
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem neg_val (r : F4Chevalley.Root) : (-r).val = -r.val := by
  change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
  simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self]

private theorem norm_bounds (r : F4Chevalley.Root) :
    1 ≤ dot r.val r.val ∧ dot r.val r.val ≤ 2 := by
  by_cases h : IsLongRoot r
  · rw [isLongRoot_norm r h]; norm_num
  · rw [isShortRoot_norm r h]; norm_num

private theorem positive_commute (m : ℕ) (r s : F4Chevalley.Root)
    (hr : typeF4RootPairing_base.IsPos r) (hs : typeF4RootPairing_base.IsPos s)
    (hd : dot r.val s.val = 0) (a b : CoefficientField m) :
    Commute (rootGeneratorInGroup m r a) (rootGeneratorInGroup m s b) := by
  have hn : dot (r.val + s.val) (r.val + s.val) =
      dot r.val r.val + dot s.val s.val := by
    change (r.val + s.val) ⬝ᵥ (r.val + s.val) = _
    rw [add_dotProduct, dotProduct_add, dotProduct_add,
      dotProduct_comm s.val r.val]
    change dot r.val r.val + dot r.val s.val +
      (dot r.val s.val + dot s.val s.val) = _
    rw [hd]; ring
  by_cases hsum : typeF4RootPairing.root r + typeF4RootPairing.root s ∈
      Set.range typeF4RootPairing.root
  · obtain ⟨t, ht⟩ := hsum
    have hn' : dot t.val t.val = dot r.val r.val + dot s.val s.val := by
      change t.val = r.val + s.val at ht
      rwa [← ht] at hn
    have hrs : IsShortRoot r := by
      intro h
      rw [isLongRoot_norm r h] at hn'
      linarith [(norm_bounds s).1, (norm_bounds t).2]
    have htl : IsLongRoot t := by
      by_contra h
      rw [isShortRoot_norm t h] at hn'
      linarith [(norm_bounds r).1, (norm_bounds s).1]
    exact Subtype.ext (rootCurve_commute_of_short_long_sum m r s t hr hs hrs htl ht a b).eq
  · have h0 : typeF4RootPairing.root r + typeF4RootPairing.root s ≠ 0 := by
      intro h
      change r.val + s.val = 0 at h
      rw [h] at hn
      have hz : dot (0 : Vec 4) 0 = 0 := by simp [dot]
      rw [hz] at hn
      linarith [(norm_bounds r).1, (norm_bounds s).1]
    exact Subtype.ext (rootCurve_commute_of_integralOperators r s
      (integralOperators_commute_of_no_sum r s hr hs h0 hsum) a b).eq

private theorem reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      r.val - (typeF4CorootScale (typeF4SimpleRootIndex i) *
        dot r.val (typeF4SimpleRoot i)) • typeF4SimpleRoot i := by
  change typeF4RootPairing.root _ = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing]
  rfl

private theorem last_flip (r : F4Chevalley.Root) :
    (wordAction (sideWord .suzuki) r).val = ![r.val 0, r.val 1, -r.val 2, -r.val 3] := by
  ext k
  fin_cases k <;>
    norm_num [wordAction, sideWord, Equiv.Perm.mul_apply, reflection_val,
      typeF4CorootScale_simpleRoot, typeF4SimpleRoot, dot, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Fin.succ]
  all_goals
    simp only [show (⟨2, by decide⟩ : Fin 4) = 2 from rfl,
      show (⟨3, by decide⟩ : Fin 4) = 3 from rfl]
    ring

private theorem action_append (w v : List (Fin 4)) (r : F4Chevalley.Root) :
    wordAction (w ++ v) r = wordAction w (wordAction v r) := by
  simp [wordAction, List.prod_append, Equiv.Perm.mul_apply]

private def firstFlipWord := interchangeWord ++ interchangeWord ++ sideWord .suzuki

private theorem first_flip (r : F4Chevalley.Root) :
    (wordAction firstFlipWord r).val = ![-r.val 0, -r.val 1, r.val 2, r.val 3] := by
  simp only [firstFlipWord, action_append, interchangeWord_action_val, last_flip]
  ext k
  fin_cases k <;> simp

private theorem commute_of_word (m : ℕ) (w : List (Fin 4)) (r s : F4Chevalley.Root)
    (a b : CoefficientField m)
    (h : Commute (rootGeneratorInGroup m (wordAction w r) a)
      (rootGeneratorInGroup m (wordAction w s) b)) :
    Commute (rootGeneratorInGroup m r a) (rootGeneratorInGroup m s b) := by
  apply Commute.of_map (MulAut.conj (simpleWord m w)).injective
  change Commute (simpleWord m w * rootGeneratorInGroup m r a * (simpleWord m w)⁻¹)
    (simpleWord m w * rootGeneratorInGroup m s b * (simpleWord m w)⁻¹)
  simpa only [simpleWord_conj_root] using h

private theorem plane_dot (r s : F4Chevalley.Root)
    (hr : r.val 0 = 0 ∧ r.val 1 = 0) (hs : s.val 2 = 0 ∧ s.val 3 = 0) :
    dot r.val s.val = 0 := by simp [dot, Fin.sum_univ_four, hr.1, hr.2, hs.1, hs.2]

private theorem last_positive_commute (m : ℕ) (r s : F4Chevalley.Root)
    (hr : r.val 0 = 0 ∧ r.val 1 = 0) (hs : s.val 2 = 0 ∧ s.val 3 = 0)
    (hp : typeF4RootPairing_base.IsPos r) (a b : CoefficientField m) :
    Commute (rootGeneratorInGroup m r a) (rootGeneratorInGroup m s b) := by
  rcases RootPairing.Base.IsPos.or_neg typeF4RootPairing_base s with hpos | hneg
  · exact positive_commute m r s hp hpos (plane_dot r s hr hs) a b
  · apply commute_of_word m firstFlipWord r s a b
    have her : wordAction firstFlipWord r = r := by
      apply Subtype.ext
      rw [first_flip]
      ext k
      fin_cases k <;> simp [hr.1, hr.2]
    have hes : wordAction firstFlipWord s = -s := by
      apply Subtype.ext
      rw [first_flip, neg_val]
      ext k
      fin_cases k <;> simp [hs.1, hs.2]
    rw [her, hes]
    apply positive_commute m r (-s) hp hneg _ a b
    apply plane_dot r (-s) hr
    rw [neg_val]
    simp [hs.1, hs.2]

/-- All signed root curves in the two orthogonal coordinate planes commute. -/
theorem root_commute (m : ℕ) (r s : F4Chevalley.Root)
    (hr : r.val 0 = 0 ∧ r.val 1 = 0) (hs : s.val 2 = 0 ∧ s.val 3 = 0)
    (a b : CoefficientField m) :
    Commute (rootGeneratorInGroup m r a) (rootGeneratorInGroup m s b) := by
  rcases RootPairing.Base.IsPos.or_neg typeF4RootPairing_base r with hpos | hneg
  · exact last_positive_commute m r s hr hs hpos a b
  · apply commute_of_word m (sideWord .suzuki) r s a b
    have her : wordAction (sideWord .suzuki) r = -r := by
      apply Subtype.ext
      rw [last_flip, neg_val]
      ext k
      fin_cases k <;> simp [hr.1, hr.2]
    have hes : wordAction (sideWord .suzuki) s = s := by
      apply Subtype.ext
      rw [last_flip]
      ext k
      fin_cases k <;> simp [hs.1, hs.2]
    rw [her, hes]
    apply last_positive_commute m (-r) s _ hs hneg a b
    rw [neg_val]
    simp [hr.1, hr.2]

private theorem block_last (p : Bool) (r : F4Chevalley.Root)
    (hr : IsSimpleBlockRoot .suzuki p r) : r.val 0 = 0 ∧ r.val 1 = 0 := by
  have h0 := hr.1 0 (by simp [leviNodes])
  have h3 := hr.1 3 (by simp [leviNodes])
  simp only [typeF4SimpleCoefficient] at h0 h3
  constructor <;> linarith

/-- The whole split B₂ Levi commutes with its Weyl conjugate. -/
theorem splitLevi_commute (m : ℕ) (x y : SplitGroup m)
    (hx : x ∈ splitLevi m .suzuki) (hy : y ∈ splitLevi m .suzuki) :
    Commute x ((interchangeElement m).val * y * (interchangeElement m).val⁻¹) := by
  let c := (MulAut.conj (interchangeElement m).val).toMonoidHom
  have hroot (p q : Bool) (r s : F4Chevalley.Root)
      (hr : IsSimpleBlockRoot .suzuki p r) (hs : IsSimpleBlockRoot .suzuki q s)
      (a b : CoefficientField m) :
      Commute (rootGeneratorInGroup m r a) (c (rootGeneratorInGroup m s b)) := by
    change Commute (rootGeneratorInGroup m r a)
      ((interchangeElement m).val * rootGeneratorInGroup m s b * (interchangeElement m).val⁻¹)
    rw [interchangeElement_conj_root]
    apply root_commute m r _ (block_last p r hr) _ a b
    simp [interchangeWord_action_val, (block_last q s hs).1, (block_last q s hs).2]
  have hright (p : Bool) (r : F4Chevalley.Root)
      (hr : IsSimpleBlockRoot .suzuki p r) (a : CoefficientField m) :
      splitLevi m .suzuki ≤ (centralizer {rootGeneratorInGroup m r a}).comap c := by
    apply sup_le
    all_goals
      apply (closure_le _).mpr
      rintro _ ⟨s, b, hs, rfl⟩
      exact mem_centralizer_singleton_iff.mpr (hroot p _ r s hr hs a b).symm.eq
  have hleft : splitLevi m .suzuki ≤
      centralizer (((splitLevi m .suzuki).map c : Subgroup (SplitGroup m)) : Set (SplitGroup m)) := by
    apply sup_le
    all_goals
      apply (closure_le _).mpr
      rintro _ ⟨r, a, hr, rfl⟩
      apply mem_centralizer_iff.mpr
      rintro _ ⟨z, hz, rfl⟩
      exact mem_centralizer_singleton_iff.mp (hright _ r hr a hz)
  exact (hleft hx (c y) (mem_map_of_mem c hy)).symm

/-- Commutation descends to the two literal exceptional fixed subgroups. -/
theorem standard_commute (m : ℕ) (x y : Model m)
    (hx : x ∈ standardSuzukiLevi m) (hy : y ∈ standardPartner m) : Commute x y := by
  obtain ⟨z, hz, rfl⟩ := hy
  apply Commute.of_map (fixedSubgroup m).subtype_injective
  exact splitLevi_commute m x.val z.val hx hz

end ReeF4.CentralCovers.OddPrimary.SuzukiOrthogonal
