module

public import Theory.SpecificGroups.ReeF4.NormalizedRootCentralizers.Torus
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.UnipotentCenter

/-!
# The full Ree Sylow center and Borel root rigidity

The genuine Borel factors as its positive unipotent subgroup times its fixed
coroot torus. Unipotent elements centralize their center, and the independent
diagonal calculation controls the torus. Together these give the required
uniform Borel centralizers for every nonidentity element of the full center.

The imported `unipotent_center_eq_longRootGroup` identifies the full center
with the concrete curve `y₅(t) = centralWord m 4 t` by fixed-coordinate
commutator calculations. The final theorem `uniform` uses that equality for
`m > 0`, so its conclusion has no center-identification or exponent premise.
The earlier conditional interfaces are preserved. In particular, central
involution classification alone would not exclude a larger center containing
elements of order four. No assertion about the derived Tits carrier is made.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927, with A.2.3–4 model
conventions; long-root words as in GLS3 Table 2.4 and 2.4.5(d).
-/

public section

namespace ReeF4.NormalizedRootCentralizers
open Parabolics EvenInvolutionGeometry Subgroup
open scoped Pointwise

/-- Combining the central-involution calculation with the independent exponent
bound identifies the whole positive-subgroup center. -/
theorem center_eq_of_central_involutions (m : ℕ)
    (hroot : ∀ t : CoefficientField m, ∀ u ∈ unipotent m,
      Commute (longRootElement m t) u)
    (hclass : ∀ x ∈ unipotent m, orderOf x = 2 →
      (∀ u ∈ unipotent m, Commute x u) →
      ∃ t : CoefficientField m, t ≠ 0 ∧ x = longRootElement m t)
    (hexp : ∀ x ∈ unipotent m, (∀ u ∈ unipotent m, Commute x u) → x ^ 2 = 1) :
    (center (unipotent m)).map (unipotent m).subtype = longRootGroup m := by
  apply le_antisymm
  · intro x hx
    obtain ⟨x, hx, rfl⟩ := hx
    change x.val ∈ longRootGroup m
    have hc : ∀ u ∈ unipotent m, Commute x.val u := by
      intro u hu
      exact (congrArg Subtype.val (mem_center_iff.mp hx ⟨u, hu⟩)).symm
    by_cases h1 : x.val = 1
    · rw [h1]
      exact one_mem _
    · have ho : orderOf x.val = 2 := orderOf_eq_prime_iff.mpr
        ⟨hexp x.val x.property hc, h1⟩
      obtain ⟨t, _, ht⟩ := hclass x.val x.property ho hc
      exact (mem_longRootGroup m _).mpr ⟨t, ht.symm⟩
  · intro x hx
    obtain ⟨t, rfl⟩ := (mem_longRootGroup m x).mp hx
    refine ⟨⟨longRootElement m t, longRootElement_mem_unipotent m t⟩,
      mem_center_iff.mpr ?_, rfl⟩
    intro u
    exact Subtype.ext (hroot t u u.property).eq.symm

private theorem borel_factors (m : ℕ) (b : Model m) (hb : b ∈ borel m) :
    ∃ u ∈ unipotent m, ∃ t ∈ fixedTorus m, u * t = b := by
  have hn := splitTorus_le_unipotent_normalizer_of_le_diagonalTorus m
    (splitTorus_eq_diagonalTorus m).le
  have ht : fixedTorus m ≤ normalizer (unipotent m : Set (Model m)) :=
    (comap_mono hn).trans (le_normalizer_comap (toSplitGroup m))
  have he := borel_eq_unipotent_sup_fixedTorus_of_splitTorus m hn
    (splitTorus_odd_card_of_le_diagonalTorus m (splitTorus_eq_diagonalTorus m).le)
  have hm : b ∈ (unipotent m : Set (Model m)) * (fixedTorus m : Set (Model m)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ ht, ← he]
    exact hb
  exact hm

/-- The coordinate calculation in the torus extends to the full genuine Borel
once the full Sylow center has been identified. This identification is an
explicit remaining premise, not a theorem asserted by this conditional result. -/
theorem uniform_of_center_eq (m : ℕ)
    (hcenter : (center (unipotent m)).map (unipotent m).subtype = longRootGroup m)
    (r : Model m) (hr : r ∈ (center (unipotent m)).map (unipotent m).subtype)
    (hne : r ≠ 1) :
    borel m ⊓ centralizer ({r} : Set (Model m)) =
      borel m ⊓ centralizer
        (((center (unipotent m)).map (unipotent m).subtype : Subgroup (Model m)) : Set (Model m)) := by
  rw [hcenter] at hr ⊢
  apply le_antisymm
  · intro b hb
    obtain ⟨u, hu, t, ht, rfl⟩ := borel_factors m b hb.1
    have huR : u ∈ centralizer (longRootGroup m : Set (Model m)) := by
      rw [← hcenter]
      apply mem_centralizer_iff.mpr
      rintro x ⟨z, hz, rfl⟩
      exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨u, hu⟩)).symm
    have hur : u ∈ centralizer ({r} : Set (Model m)) :=
      centralizer_le (Set.singleton_subset_iff.mpr hr) huR
    have htr : t ∈ centralizer ({r} : Set (Model m)) := by
      have hh := (centralizer ({r} : Set (Model m))).mul_mem
        ((centralizer ({r} : Set (Model m))).inv_mem hur) hb.2
      simpa only [inv_mul_cancel_left] using hh
    have htR : t ∈ centralizer (longRootGroup m : Set (Model m)) :=
      (show t ∈ fixedTorus m ⊓ centralizer (longRootGroup m : Set (Model m)) from
        fixedTorus_centralizers m r hr hne ▸ ⟨ht, htr⟩).2
    exact ⟨hb.1, (centralizer (longRootGroup m : Set (Model m))).mul_mem huR htR⟩
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr hr))

/-- Application of the two independent center calculations to every
nonidentity element of the full center, including the marked element a*. -/
theorem uniform_of_central_involutions (m : ℕ)
    (hroot : ∀ t : CoefficientField m, ∀ u ∈ unipotent m,
      Commute (longRootElement m t) u)
    (hclass : ∀ x ∈ unipotent m, orderOf x = 2 →
      (∀ u ∈ unipotent m, Commute x u) →
      ∃ t : CoefficientField m, t ≠ 0 ∧ x = longRootElement m t)
    (hexp : ∀ x ∈ unipotent m, (∀ u ∈ unipotent m, Commute x u) → x ^ 2 = 1)
    (r : Model m) (hr : r ∈ (center (unipotent m)).map (unipotent m).subtype)
    (hne : r ≠ 1) :
    borel m ⊓ centralizer ({r} : Set (Model m)) =
      borel m ⊓ centralizer
        (((center (unipotent m)).map (unipotent m).subtype : Subgroup (Model m)) : Set (Model m)) :=
  uniform_of_center_eq m (center_eq_of_central_involutions m hroot hclass hexp) r hr hne

/-- For `q = 2^(2*m+1) > 2`, every nonidentity element of the full positive
Ree center has the same centralizer in the genuine Borel as the whole center.
The full center identification is supplied by the fixed-coordinate calculation. -/
theorem uniform (m : ℕ) (hm : 0 < m)
    (r : Model m) (hr : r ∈ (center (unipotent m)).map (unipotent m).subtype)
    (hne : r ≠ 1) :
    borel m ⊓ centralizer ({r} : Set (Model m)) =
      borel m ⊓ centralizer
        (((center (unipotent m)).map (unipotent m).subtype : Subgroup (Model m)) :
          Set (Model m)) :=
  uniform_of_center_eq m (unipotent_center_eq_longRootGroup m hm) r hr hne

end ReeF4.NormalizedRootCentralizers
