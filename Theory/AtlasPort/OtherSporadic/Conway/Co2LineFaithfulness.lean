/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co2LineFaithfulness.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co2NormalGeneration
public import Theory.AtlasPort.OtherSporadic.Conway.MinimumShapeInvariance
public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu24Alternating

/-!
Faithfulness of the norm-four vector stabilizer on orthogonal minimum lines.
The concrete coordinate vectors force an isometry fixing all such lines to act trivially.

Source: Gerald Höhn, `Atlas/Conway/Co2LineFaithfulness.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 10000

/-- Magnitude support of a minimum vector on two distinct coordinate axes. -/
theorem minimumPairPlus_support (a b : Omega) (hab : a ≠ b) :
    evenMagnitudeSupport (minimumPairPlus a b).val 4 = {a,b} := by
  ext k
  simp only [evenMagnitudeSupport,Finset.mem_filter,Finset.mem_univ,true_and,
    minimumPairPlus,Pi.add_apply,coordinateVector,Pi.single_apply,
    Finset.mem_insert,Finset.mem_singleton]
  by_cases ha : k = a
  · subst k; simp [hab]
  by_cases hb : k = b
  · subst k; simp [Ne.symm hab]
  simp [ha,hb]

theorem evenMagnitudeSupport_neg (x : IntegerCoordinates) (k : ℤ) :
    evenMagnitudeSupport (-x) k = evenMagnitudeSupport x k := by
  simp [evenMagnitudeSupport]

theorem monomial_pair_line_support (m : GolayMonomialGroup) (a b : Omega) (hab : a ≠ b)
    (h : antipodalLine ((monomialEmbedding m).val (minimumPairPlus a b)) =
      antipodalLine (minimumPairPlus a b)) :
    permuteBlock m.right.val {a,b} = {a,b} := by
  have he := monomial_magnitude_support m (minimumPairPlus a b) 4
  rcases (antipodalLine_eq_iff _ _).mp h with h | h
  · rw [h,minimumPairPlus_support a b hab] at he
    exact he.symm
  · rw [h,show (-(minimumPairPlus a b)).val = -(minimumPairPlus a b).val from rfl,
      evenMagnitudeSupport_neg,minimumPairPlus_support a b hab] at he
    exact he.symm

theorem marked_pair_orthogonal (a b : Omega)
    (ha : a ≠ ((0,0),0)) (ha' : a ≠ ((0,0),1))
    (hb : b ≠ ((0,0),0)) (hb' : b ≠ ((0,0),1)) :
    integerDot (minimumPairPlus ((0,0),0) ((0,0),1)).val
      (minimumPairPlus a b).val = 0 := by
  have h : ∀ a b : Omega, a ≠ ((0,0),0) → a ≠ ((0,0),1) →
      b ≠ ((0,0),0) → b ≠ ((0,0),1) →
      integerDot (minimumPairPlus ((0,0),0) ((0,0),1)).val (minimumPairPlus a b).val = 0 := by
    decide +kernel
  exact h a b ha ha' hb hb'

theorem marked_permutation_eq_one (p : Mathieu24CodeModel)
    (h : ∀ a b : Omega, a ≠ ((0,0),0) → a ≠ ((0,0),1) →
      b ≠ ((0,0),0) → b ≠ ((0,0),1) → a ≠ b → permuteBlock p.val {a,b} = {a,b}) : p = 1 := by
  have hfix (a : Omega) (ha : a ≠ ((0,0),0)) (ha' : a ≠ ((0,0),1)) : p.val a = a := by
    have hfresh : ∀ a t : Omega, ∃ b : Omega,
        b ≠ ((0,0),0) ∧ b ≠ ((0,0),1) ∧ b ≠ a ∧ b ≠ t := by decide +kernel
    obtain ⟨b,hb,hb',hba,hbt⟩ := hfresh a (p.val a)
    have hp : p.val a ∈ permuteBlock p.val {a,b} :=
      Finset.mem_image.mpr ⟨a,Finset.mem_insert_self _ _,rfl⟩
    rw [h a b ha ha' hb hb' hba.symm] at hp
    rcases Finset.mem_insert.mp hp with he | he
    · exact he
    · exact (hbt (Finset.mem_singleton.mp he).symm).elim
  apply Subtype.ext
  by_contra hn
  have hs : p.val.support ⊆ {((0,0),0),((0,0),1)} := by
    intro a ha
    by_contra hh
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hh
    exact (Equiv.Perm.mem_support.mp ha) (hfix a hh.1 hh.2)
  have hc : p.val.support.card = 2 := le_antisymm
    ((Finset.card_le_card hs).trans (by decide))
    (Equiv.Perm.two_le_card_support_of_ne_one hn)
  have hswap := Equiv.Perm.card_support_eq_two.mp hc
  have hsign := Equiv.Perm.mem_alternatingGroup.mp (mathieu24_le_alternating p.prop)
  rw [hswap.sign_eq] at hsign
  exact (by decide : (-1 : ℤˣ) ≠ 1) hsign

theorem sign_pair_line_equal (c : golay) (a b : Omega) (hab : a ≠ b)
    (h : antipodalLine ((signIsometry c).val (minimumPairPlus a b)) =
      antipodalLine (minimumPairPlus a b)) : c.val a = c.val b := by
  have ha : (minimumPairPlus a b).val a = 4 := by
    simp [minimumPairPlus,coordinateVector,hab]
  have hb : (minimumPairPlus a b).val b = 4 := by
    simp [minimumPairPlus,coordinateVector,hab.symm]
  rcases (antipodalLine_eq_iff _ _).mp h with h | h
  all_goals
    have h0 := congrArg (fun x : leech => x.val a) h
    have h1 := congrArg (fun x : leech => x.val b) h
    change (if c.val a = 0 then (minimumPairPlus a b).val a else
      -(minimumPairPlus a b).val a) = _ at h0
    change (if c.val b = 0 then (minimumPairPlus a b).val b else
      -(minimumPairPlus a b).val b) = _ at h1
    rw [ha] at h0
    rw [hb] at h1
    rcases bit_cases (c.val a) with ha0 | ha1 <;>
      rcases bit_cases (c.val b) with hb0 | hb1 <;>
      simp_all

theorem shortened_sign_eq_zero_of_pair_lines (c : golay)
    (hi : c.val ((0,0),0) = 0) (hj : c.val ((0,0),1) = 0)
    (h : ∀ a b : Omega, a ≠ ((0,0),0) → a ≠ ((0,0),1) →
      b ≠ ((0,0),0) → b ≠ ((0,0),1) → a ≠ b →
      antipodalLine ((signIsometry c).val (minimumPairPlus a b)) =
        antipodalLine (minimumPairPlus a b)) : c = 0 := by
  have hconst (a : Omega) (ha : a ≠ ((0,0),0)) (ha' : a ≠ ((0,0),1)) :
      c.val a = c.val ((0,0),2) := by
    by_cases he : a = ((0,0),2)
    · rw [he]
    exact sign_pair_line_equal c a ((0,0),2) he
      (h a ((0,0),2) ha ha' (by decide) (by decide) he)
  rcases bit_cases (c.val ((0,0),2)) with hz | ho
  · apply Subtype.ext
    funext a
    by_cases ha : a = ((0,0),0)
    · subst a; exact hi
    by_cases hb : a = ((0,0),1)
    · subst a; exact hj
    exact (hconst a ha hb).trans hz
  · have hv : c.val = fun a => if a = ((0,0),0) ∨ a = ((0,0),1) then 0 else 1 := by
      funext a
      by_cases ha : a = ((0,0),0)
      · subst a; simp [hi]
      by_cases hb : a = ((0,0),1)
      · subst a; simp [hj]
      simp [ha,hb,hconst a ha hb,ho]
    have hw := golay_weights c
    rw [hv] at hw
    have hn : hammingNorm (fun a : Omega =>
        if a = ((0,0),0) ∨ a = ((0,0),1) then (0 : Bit) else 1) = 22 := by decide +kernel
    rw [hn] at hw
    norm_num at hw

theorem co2_fixes_lines_eq_one (g : Co2MarkedModel)
    (hg : ∀ l : Atlas.Sporadic.Conway2.Points, g • l = l) : g = 1 := by
  have hlocal : g ∈ Atlas.Sporadic.Conway2.LocalGroup := by
    rw [← Atlas.Sporadic.Conway2.full_point_stabilizer]
    exact hg Atlas.Sporadic.Conway2.basePoint
  have hmono : g.val ∈ monomialSubgroup :=
    (le_of_eq (orthogonalLineStabilizer_eq_monomial _ _ (by decide))) hlocal
  obtain ⟨m,hm⟩ := hmono
  have hlines (a b : Omega) (ha : a ≠ ((0,0),0)) (ha' : a ≠ ((0,0),1))
      (hb : b ≠ ((0,0),0)) (hb' : b ≠ ((0,0),1)) (hab : a ≠ b) :
      antipodalLine (g.val.val (minimumPairPlus a b)) = antipodalLine (minimumPairPlus a b) := by
    let l : Atlas.Sporadic.Conway2.Points := toAntipodalImage _
      ⟨minimumPairPlus a b,minimumPairPlus_norm a b hab,marked_pair_orthogonal a b ha ha' hb hb'⟩
    have hh := congrArg (fun l : Atlas.Sporadic.Conway2.Points => l.val) (hg l)
    change leechCentralProjection g.val • antipodalLine (minimumPairPlus a b) =
      antipodalLine (minimumPairPlus a b) at hh
    rwa [projection_antipodalLine] at hh
  have hp : m.right = 1 := by
    apply marked_permutation_eq_one
    intro a b ha ha' hb hb' hab
    apply monomial_pair_line_support m a b hab
    rw [hm]
    exact hlines a b ha ha' hb hb' hab
  have hs : g.val = signIsometry m.left.toAdd := by
    rw [← hm]
    change signIsometry m.left.toAdd * permutationEmbedding m.right = signIsometry m.left.toAdd
    rw [hp,map_one,mul_one]
  have hc : m.left.toAdd.val ((0,0),0) = 0 ∧ m.left.toAdd.val ((0,0),1) = 0 := by
    have hf : (signIsometry m.left.toAdd).val (minimumPairPlus ((0,0),0) ((0,0),1)) =
        minimumPairPlus ((0,0),0) ((0,0),1) := hs ▸ g.prop
    constructor
    · have he := congrArg (fun x : leech => x.val ((0,0),0)) hf
      change (if m.left.toAdd.val ((0,0),0) = 0 then 4 else -4) = (4 : ℤ) at he
      by_contra hh
      simp [hh] at he
    · have he := congrArg (fun x : leech => x.val ((0,0),1)) hf
      change (if m.left.toAdd.val ((0,0),1) = 0 then 4 else -4) = (4 : ℤ) at he
      by_contra hh
      simp [hh] at he
  have hz : m.left.toAdd = 0 := by
    apply shortened_sign_eq_zero_of_pair_lines _ hc.1 hc.2
    intro a b ha ha' hb hb' hab
    rw [← hs]
    exact hlines a b ha ha' hb hb' hab
  apply Subtype.ext
  rw [hs,hz]
  exact signEmbedding.map_one

theorem co2_lines_faithful : FaithfulSMul Co2MarkedModel Atlas.Sporadic.Conway2.Points where
  eq_of_smul_eq_smul {g h} he := by
    have hh : g⁻¹*h = 1 := co2_fixes_lines_eq_one _ (by
      intro l
      rw [mul_smul,← he l,inv_smul_smul])
    exact inv_mul_eq_one.mp hh

end Atlas.Conway
