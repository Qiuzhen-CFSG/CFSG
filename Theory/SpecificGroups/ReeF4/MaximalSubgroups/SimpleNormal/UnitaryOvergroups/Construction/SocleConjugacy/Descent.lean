module

public import Theory.SpecificGroups.ReeF4.Model
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

/-!
# Descent of split conjugators to the Ree fixed subgroup

For two subgroups fixed pointwise by the Ree twist, a split conjugator `x`
has defect `x⁻¹ * reeTwist m x` in the centralizer of its source. The twist
inverts this defect. A right correction `c` in the source normalizer with
`c * (reeTwist m c)⁻¹ = x⁻¹ * reeTwist m x` makes `x * c` fixed and leaves
its subgroup image unchanged. Injectivity of the actual Ree inclusion then
descends the equality of subgroups.

If the defect has odd order, a power of it is a square root and gives such
a correction in the centralizer. Oddness of the entire split centralizer is
one sufficient condition, not an assertion about unitary subgroups here.

This is an elementary fixed-subgroup argument for the concrete construction
in `ReeF4.Model`. Its intended application is the PGU₃ case of Malle,
J. Algebra 139 (1991), 52–69, DOI 10.1016/0021-8693(91)90283-E.
It neither supplies a split conjugator nor computes the unitary centralizer.
-/

public noncomputable section

namespace ReeF4.MaximalSubgroups.SimpleNormal.Construction

open Subgroup

/-- Pointwise fixedness places the twist defect in the source centralizer. -/
theorem split_twist_defect_mem_centralizer {m : ℕ}
    (H K : Subgroup (Model m)) (x : SplitGroup m)
    (hx : (H.map (toSplitGroup m)).map (MulAut.conj x).toMonoidHom =
      K.map (toSplitGroup m)) :
    x⁻¹ * reeTwist m x ∈ centralizer (H.map (toSplitGroup m) : Set (SplitGroup m)) := by
  apply mem_centralizer_iff.mpr
  rintro z ⟨h, hh, rfl⟩
  have hz : x * toSplitGroup m h * x⁻¹ ∈ K.map (toSplitGroup m) := by
    rw [← hx]
    exact ⟨toSplitGroup m h, ⟨h, hh, rfl⟩, rfl⟩
  obtain ⟨k, _, hk⟩ := hz
  have he := congrArg (reeTwist m) hk
  simp only [reeTwist_toSplitGroup, map_mul, map_inv] at he
  have heq : reeTwist m x * toSplitGroup m h * (reeTwist m x)⁻¹ =
      x * toSplitGroup m h * x⁻¹ := he.symm.trans hk
  have heq' := congrArg (fun a => x⁻¹ * a * reeTwist m x) heq
  group at heq'
  simpa only [zpow_neg_one, mul_assoc] using heq'.symm

/-- The involutive twist inverts every conjugator defect. -/
theorem split_twist_defect_inverted {m : ℕ} (x : SplitGroup m) :
    reeTwist m (x⁻¹ * reeTwist m x) = (x⁻¹ * reeTwist m x)⁻¹ := by
  simp only [map_mul, map_inv, reeTwist_involutive m x, mul_inv_rev, inv_inv]

/-- A normalizer correction descends the exact subgroup equality, without
prescribing a marking of either subgroup. -/
theorem conjugacy_of_split_conjugacy_and_correction {m : ℕ}
    (H K : Subgroup (Model m)) (x c : SplitGroup m)
    (hx : (H.map (toSplitGroup m)).map (MulAut.conj x).toMonoidHom =
      K.map (toSplitGroup m))
    (hc : c ∈ normalizer (H.map (toSplitGroup m) : Set (SplitGroup m)))
    (he : c * (reeTwist m c)⁻¹ = x⁻¹ * reeTwist m x) :
    ∃ g : Model m, H.map (MulAut.conj g).toMonoidHom = K := by
  have hsig : reeTwist m x = x * c * (reeTwist m c)⁻¹ := by
    calc
      reeTwist m x = x * (x⁻¹ * reeTwist m x) := by group
      _ = x * (c * (reeTwist m c)⁻¹) := by rw [he]
      _ = x * c * (reeTwist m c)⁻¹ := by group
  have hfix : reeTwist m (x * c) = x * c := by
    rw [map_mul, hsig]
    group
  let g : Model m := ⟨x * c, (mem_fixedSubgroup m (x * c)).mpr hfix⟩
  refine ⟨g, map_injective (toSplitGroup_injective m) ?_⟩
  calc
    (H.map (MulAut.conj g).toMonoidHom).map (toSplitGroup m) =
        (H.map (toSplitGroup m)).map (MulAut.conj (x * c)).toMonoidHom := by
      rw [map_map, map_map]
      congr 1
      apply MonoidHom.ext
      intro z
      change toSplitGroup m (g * z * g⁻¹) =
        (x * c) * toSplitGroup m z * (x * c)⁻¹
      simp only [map_mul, map_inv, toSplitGroup_apply, g]
    _ = ((H.map (toSplitGroup m)).map (MulAut.conj c).toMonoidHom).map
        (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.map_map (H.map (toSplitGroup m))
        (MulAut.conj x).toMonoidHom (MulAut.conj c).toMonoidHom]
      congr 1
      apply MonoidHom.ext
      intro z
      simp [MulAut.conj_apply, mul_assoc]
    _ = (H.map (toSplitGroup m)).map (MulAut.conj x).toMonoidHom := by
      have hcmap : (H.map (toSplitGroup m)).map (MulAut.conj c).toMonoidHom =
          H.map (toSplitGroup m) := mem_normalizer_iff_map_conj_eq.mp hc
      rw [hcmap]
    _ = K.map (toSplitGroup m) := hx

/-- An odd-order defect has a square root in its own cyclic subgroup.
This gives a centralizer correction with the required orientation. -/
theorem twist_correction_of_odd_defect {m : ℕ}
    (H K : Subgroup (Model m)) (x : SplitGroup m)
    (hx : (H.map (toSplitGroup m)).map (MulAut.conj x).toMonoidHom =
      K.map (toSplitGroup m))
    (hodd : Odd (orderOf (x⁻¹ * reeTwist m x))) :
    ∃ c : SplitGroup m, c ∈ centralizer (H.map (toSplitGroup m) : Set (SplitGroup m)) ∧
      c * (reeTwist m c)⁻¹ = x⁻¹ * reeTwist m x := by
  let d := x⁻¹ * reeTwist m x
  have hd := split_twist_defect_mem_centralizer H K x hx
  obtain ⟨k, hk⟩ := exists_pow_eq_pow_two_mul (pow_orderOf_eq_one d) hodd 1
  refine ⟨d ^ k, (centralizer _).pow_mem hd k, ?_⟩
  have hinv : reeTwist m d = d⁻¹ := split_twist_defect_inverted x
  calc
    d ^ k * (reeTwist m (d ^ k))⁻¹ = (d ^ k) ^ 2 := by
      rw [map_pow, hinv, inv_pow, inv_inv, pow_two]
    _ = d := by
      rw [← pow_mul, Nat.mul_comm k 2]
      simpa only [pow_one] using hk.symm

/-- An odd split centralizer suffices for the correction equation. -/
theorem twist_correction_of_odd_centralizer {m : ℕ}
    (H K : Subgroup (Model m)) (x : SplitGroup m)
    (hx : (H.map (toSplitGroup m)).map (MulAut.conj x).toMonoidHom =
      K.map (toSplitGroup m))
    (hodd : Odd (Nat.card (centralizer (H.map (toSplitGroup m) : Set (SplitGroup m))))) :
    ∃ c : SplitGroup m, c ∈ centralizer (H.map (toSplitGroup m) : Set (SplitGroup m)) ∧
      c * (reeTwist m c)⁻¹ = x⁻¹ * reeTwist m x := by
  have hd := split_twist_defect_mem_centralizer H K x hx
  exact twist_correction_of_odd_defect H K x hx
    (hodd.of_dvd_nat ((centralizer _).orderOf_dvd_natCard hd))

/-- Split conjugacy descends when the source split centralizer has odd order. -/
theorem conjugacy_of_split_conjugacy_of_odd_centralizer {m : ℕ}
    (H K : Subgroup (Model m)) (x : SplitGroup m)
    (hx : (H.map (toSplitGroup m)).map (MulAut.conj x).toMonoidHom =
      K.map (toSplitGroup m))
    (hodd : Odd (Nat.card (centralizer (H.map (toSplitGroup m) : Set (SplitGroup m))))) :
    ∃ g : Model m, H.map (MulAut.conj g).toMonoidHom = K := by
  obtain ⟨c, hc, he⟩ := twist_correction_of_odd_centralizer H K x hx hodd
  exact conjugacy_of_split_conjugacy_and_correction H K x c hx
    (centralizer_le_normalizer _ hc) he

end ReeF4.MaximalSubgroups.SimpleNormal.Construction
