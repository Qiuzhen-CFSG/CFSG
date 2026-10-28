module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.RootPair
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedIntersection
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.RootTransport
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover

/-!
# The opposition Bruhat cell in the actual Ree fixed group

Fixed-point Bruhat coverage writes every element as `u * n * v`,
where `u` and `v` belong to the actual positive fixed subgroup and `n` acts
on the split root curves by a root permutation and nonzero scalar factors.
Disjointness is unchanged on removing the two unipotent factors. The twist's
involution property detects split intersections, and root-curve injectivity
then forces `n` to send the positive subgroup onto the negative subgroup.
Comparison with any supplied opposition element `w` makes `w⁻¹ * n` normalize
the positive subgroup, giving the requested normalizer double coset.

All conjugations here are left conjugations: `MulAut.conj n` sends `y` to
`n * y * n⁻¹`. No opposition representative is constructed in this module.
The final theorem discharges fixed-point Bruhat coverage for `m ≥ 1` using
the split normal forms and their uniqueness in `FixedBruhatCover`. It requires
no simplicity, perfectness or odd-index premise.

Source: GLS3 2.3.4–2.3.8, particularly the normal form in 2.3.5 and the
nonidentity root intersections in 2.3.7–2.3.8(c), in
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open Subgroup

private theorem map_aut_mul {G : Type*} [Group G] (H : Subgroup G) (a b : MulAut G) :
    H.map (a * b).toMonoidHom = (H.map b.toMonoidHom).map a.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem disjoint_of_normalizer_factors {G : Type*} [Group G]
    (U : Subgroup G) {u n v : G} (hu : u ∈ normalizer U) (hv : v ∈ normalizer U)
    (hd : Disjoint U (U.map (MulAut.conj (u * n * v)).toMonoidHom)) :
    Disjoint U (U.map (MulAut.conj n).toMonoidHom) := by
  have hu' : U.map (MulAut.conj u).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hu
  have hv' : U.map (MulAut.conj v).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hv
  rw [map_mul, map_mul, map_aut_mul, map_aut_mul, hv'] at hd
  conv_lhs at hd => rw [← hu']
  have h := Subgroup.disjoint_map (f := ((MulAut.conj u)⁻¹).toMonoidHom)
    ((MulAut.conj u)⁻¹).injective hd
  simp only [← map_aut_mul, inv_mul_cancel, inv_mul_cancel_left] at h
  change Disjoint (U.map (MonoidHom.id G)) (U.map (MulAut.conj n).toMonoidHom) at h
  simpa only [Subgroup.map_id] using h

namespace ReeF4.LocalBlockInput.PairNormalization.OppositionCell

/-- A root-permuting fixed element whose positive conjugate is disjoint
sends the actual positive fixed subgroup onto the actual negative one. -/
theorem RootTransport.map_standardUnipotent_eq_opposite_of_disjoint
    {m : ℕ} (d : LocalBlockInput m) (n : d.fixedGroup) (a : RootTransport n.val)
    (hd : Disjoint (LargeLocalSeeds.standardUnipotent d)
      ((LargeLocalSeeds.standardUnipotent d).map (MulAut.conj n).toMonoidHom)) :
    (LargeLocalSeeds.standardUnipotent d).map (MulAut.conj n).toMonoidHom =
      oppositeUnipotent d := by
  have hs := a.map_positive_eq_negative_of_disjoint
    (splitUnipotent_disjoint_conjugate_of_fixed_disjoint d n hd)
  rw [LargeLocalSeeds.standardUnipotent, map_conj_subgroupOf, hs]
  rfl

/-- The opposition-cell criterion conditional on genuine fixed-point Bruhat
coverage. The coverage premise is independent of the supplied `w` and must
be established for the criterion; the final theorem below discharges it. -/
theorem exists_normalizer_factors_of_root_bruhat
    {m : ℕ} (d : LocalBlockInput m)
    (hbruhat : ∀ x : d.fixedGroup,
      ∃ u ∈ LargeLocalSeeds.standardUnipotent d, ∃ n : d.fixedGroup,
        Nonempty (RootTransport n.val) ∧
        ∃ v ∈ LargeLocalSeeds.standardUnipotent d, x = u * n * v)
    (w : d.fixedGroup)
    (hw : (LargeLocalSeeds.standardUnipotent d).map (MulAut.conj w).toMonoidHom =
      oppositeUnipotent d)
    (x : d.fixedGroup)
    (hd : Disjoint (LargeLocalSeeds.standardUnipotent d)
      ((LargeLocalSeeds.standardUnipotent d).map (MulAut.conj x).toMonoidHom)) :
    ∃ b ∈ Subgroup.normalizer (LargeLocalSeeds.standardUnipotent d),
      ∃ c ∈ Subgroup.normalizer (LargeLocalSeeds.standardUnipotent d), x = b * w * c := by
  obtain ⟨u, hu, n, ⟨a⟩, v, hv, hx⟩ := hbruhat x
  have huN := Subgroup.le_normalizer hu
  have hvN := Subgroup.le_normalizer hv
  have hdn := disjoint_of_normalizer_factors (LargeLocalSeeds.standardUnipotent d)
    huN hvN (hx ▸ hd)
  have hn := a.map_standardUnipotent_eq_opposite_of_disjoint d n hdn
  have hnN : w⁻¹ * n ∈ Subgroup.normalizer (LargeLocalSeeds.standardUnipotent d) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (LargeLocalSeeds.standardUnipotent d).map
      (MulAut.conj (w⁻¹ * n)).toMonoidHom = LargeLocalSeeds.standardUnipotent d
    rw [map_mul, map_aut_mul, hn, ← hw, ← map_aut_mul, ← map_mul, inv_mul_cancel,
      map_one]
    exact Subgroup.map_id _
  refine ⟨u, huN, w⁻¹ * n * v, (Subgroup.normalizer _).mul_mem hnN hvN, ?_⟩
  rw [hx]
  group

/-- A conjugate disjoint from the positive fixed subgroup lies in the
opposition normalizer double coset. The fixed-point Bruhat decomposition and
the root-intersection argument discharge every geometric premise except the
specified opposition representative `w`. -/
theorem exists_normalizer_factors_of_disjoint
    {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m) (w : d.fixedGroup)
    (hw : (LargeLocalSeeds.standardUnipotent d).map (MulAut.conj w).toMonoidHom =
      oppositeUnipotent d)
    (x : d.fixedGroup)
    (hd : Disjoint (LargeLocalSeeds.standardUnipotent d)
      ((LargeLocalSeeds.standardUnipotent d).map (MulAut.conj x).toMonoidHom)) :
    ∃ b ∈ Subgroup.normalizer (LargeLocalSeeds.standardUnipotent d),
      ∃ c ∈ Subgroup.normalizer (LargeLocalSeeds.standardUnipotent d), x = b * w * c :=
  exists_normalizer_factors_of_root_bruhat d (FixedBruhatCover.exists_root_bruhat hm d)
    w hw x hd

end ReeF4.LocalBlockInput.PairNormalization.OppositionCell
end
