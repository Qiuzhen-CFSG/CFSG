module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport.PlaneCharts.Geometry
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport.PlaneCharts.Placement.FiniteCertificate

/-!
# Simultaneous Weyl placement of two F4 roots

Every pair of the literal real-coordinate F4 roots can be moved by one word in
the actual simple reflections into the real span of two displayed simple roots.
The finite certificate lists twice the root coordinates and a decreasing
distance to the standard planes. We prove that its list covers the source root
set, that its reflection table is the action of `typeF4RootPairing`, and that
its terminal zero coefficients give membership in the specified real span.
Induction on the distance then constructs the required `reflectionWord`, with
the new simple reflection appended on the right to respect its action order.

No independence hypothesis is used: equal and opposite roots are included.
`hasPlanePlacement` discharges exactly the geometric premise of
`hasPairPlaneCharts_of_placement` in the sibling `PlaneCharts` module.

Source: GLS3 §2.9.3, `refs/KGroup/GLS3/chapter2.tex`, lines 1455–1462.
-/

public section

namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.PlaneCharts
namespace PlacementCertificate
open Theory.AlgebraicGroup.StandardRootSystem RootPairing.IntegralGeckConstruction

private noncomputable def realize (v : Fin 4 → ℤ) : Vec 4 := fun k => (v k : ℝ) / 2

private lemma simple_realize (i : Fin 4) : typeF4SimpleRoot i = realize (simple i) := by
  fin_cases i <;> ext k <;> fin_cases k <;> norm_num [typeF4SimpleRoot, realize, simple]

private lemma dot_realize (v w : Fin 4 → ℤ) :
    dot (realize v) (realize w) = ((∑ k, v k * w k : ℤ) : ℝ) / 4 := by
  simp only [dot, realize, Fin.sum_univ_four, Int.cast_add, Int.cast_mul]
  ring

private lemma coefficient_realize (v : Fin 4 → ℤ) (k : Fin 4) :
    typeF4SimpleCoefficient (realize v) k = (coefficient v k : ℝ) / 2 := by
  fin_cases k <;>
    simp [typeF4SimpleCoefficient, coefficient, realize] <;> ring

private lemma root_coverage (r : typeF4Roots) : ∃ a : Fin 48, r.val = realize (coords a) := by
  rcases r.property with (hp | hu) | hh
  · obtain ⟨i, j, hij, s, t, hs, ht, hr⟩ := hp
    have sign (x : ℝ) (hx : x ∈ ({-1, 1} : Set ℝ)) :
        ∃ b : Bool, x = if b then 1 else -1 := by
      rcases hx with hx | hx
      · exact ⟨false, hx⟩
      · exact ⟨true, hx⟩
    obtain ⟨u, rfl⟩ := sign s hs
    obtain ⟨v, rfl⟩ := sign t ht
    obtain ⟨a, ha⟩ := pair_coverage i j hij u v
    refine ⟨a, ?_⟩
    rw [hr]
    ext k
    simp only [realize, ha, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      basisVector, Pi.single_apply, Int.cast_add, Int.cast_ite]
    cases u <;> cases v <;> split_ifs <;> norm_num
  · obtain ⟨i, hi | hi⟩ := hu
    · obtain ⟨a, ha⟩ := unit_coverage i true
      refine ⟨a, ?_⟩
      rw [hi]
      ext k
      simp [realize, ha, basisVector, Pi.single_apply]
      split_ifs <;> norm_num
    · obtain ⟨a, ha⟩ := unit_coverage i false
      refine ⟨a, ?_⟩
      rw [hi]
      ext k
      simp [realize, ha, basisVector, Pi.single_apply]
      split_ifs <;> norm_num
  · obtain ⟨ε, hε⟩ := hh
    obtain ⟨a, ha⟩ := half_coverage ε
    refine ⟨a, ?_⟩
    rw [← hε]
    ext k
    simp [halfSignVector, realize, ha]
    split_ifs <;> norm_num

private lemma reflection_realize (i : Fin 4) (a : Fin 48) (r : typeF4Roots)
    (hr : r.val = realize (coords a)) :
    (typeF4RootPairing.reflectionPerm (sourceIndex i) r).val =
      realize (coords (reflect i a)) := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ _) = _
  rw [typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.reflection_apply_root]
  simp only [sourceIndex, typeF4RootPairing_baseEquiv_val, typeF4RootPairing_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot, typeF4SimpleRootIndex_val]
  rw [hr, simple_realize, dot_realize]
  ext k
  have h : (4 : ℝ) * (coords (reflect i a) k : ℝ) =
      4 * (coords a k : ℝ) - (if i.val < 2 then 1 else 2) *
        ((∑ t : Fin 4, coords a t * simple i t : ℤ) : ℝ) * (simple i k : ℝ) := by
    exact_mod_cast reflection_valid i a k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, realize]
  linear_combination -h / 8

private lemma inPlane_realize (a : Fin 48) (i j : Fin 4) (r : typeF4Roots)
    (hr : r.val = realize (coords a)) (h : InPlane a i j) :
    r ∈ rootPlane (signedRoot true i) (signedRoot true j) := by
  change r.val ∈ Submodule.span ℝ {typeF4SimpleRoot i, typeF4SimpleRoot j}
  rw [hr, ← typeF4SimpleCoefficient_reconstruction (realize (coords a))]
  apply Submodule.sum_mem
  intro k _
  by_cases hki : k = i
  · subst k
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
  by_cases hkj : k = j
  · subst k
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [coefficient_realize, h k hki hkj]
  simp only [Int.cast_zero, zero_div, zero_smul]
  exact Submodule.zero_mem _

private def Placeable (r s : typeF4Roots) : Prop :=
  ∃ (w : List typeF4RootPairing_base.support) (i j : Fin 4),
    reflectionWord (P := typeF4RootPairing) w r ∈
        rootPlane (signedRoot true i) (signedRoot true j) ∧
      reflectionWord (P := typeF4RootPairing) w s ∈
        rootPlane (signedRoot true i) (signedRoot true j)

private lemma reflectionWord_append_placement (u v : List typeF4RootPairing_base.support)
    (r : typeF4Roots) :
    reflectionWord (P := typeF4RootPairing) (u ++ v) r =
      reflectionWord (P := typeF4RootPairing) u (reflectionWord v r) := by
  induction u with
  | nil => rfl
  | cons i u ih => simp only [List.cons_append, reflectionWord, ih]

private lemma placeable_of_coordinates (n : ℕ) : ∀ a b : Fin 48,
    (certificate a b).1 = n → ∀ r s : typeF4Roots,
    r.val = realize (coords a) → s.val = realize (coords b) → Placeable r s := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b hn r s hr hs
    have hv := valid a b
    unfold Valid at hv
    by_cases hz : (certificate a b).1 = 0
    · rw [if_pos hz] at hv
      exact ⟨[], (certificate a b).2.1, (certificate a b).2.2,
        inPlane_realize a _ _ r hr hv.1, inPlane_realize b _ _ s hs hv.2⟩
    · rw [if_neg hz] at hv
      obtain ⟨w, i, j, hw₁, hw₂⟩ := ih _ (by simpa only [hn] using hv)
        (reflect (certificate a b).2.1 a) (reflect (certificate a b).2.1 b) rfl
        (typeF4RootPairing.reflectionPerm (sourceIndex (certificate a b).2.1) r)
        (typeF4RootPairing.reflectionPerm (sourceIndex (certificate a b).2.1) s)
        (reflection_realize _ a r hr) (reflection_realize _ b s hs)
      refine ⟨w ++ [sourceIndex (certificate a b).2.1], i, j, ?_, ?_⟩
      · simpa only [reflectionWord_append_placement, reflectionWord] using hw₁
      · simpa only [reflectionWord_append_placement, reflectionWord] using hw₂

end PlacementCertificate

/-- A single Weyl word places both roots in one standard pair's real span.
This includes equal, opposite, and all independent pairs. -/
theorem hasPlanePlacement : HasPlanePlacement := by
  intro r s
  obtain ⟨a, ha⟩ := PlacementCertificate.root_coverage r
  obtain ⟨b, hb⟩ := PlacementCertificate.root_coverage s
  exact PlacementCertificate.placeable_of_coordinates _ a b rfl r s ha hb

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.PlaneCharts
