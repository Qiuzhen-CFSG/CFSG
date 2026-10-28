module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.RootPair
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.Disjoint
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.WeylOpposition

/-!
# Simultaneous normalization of the Ree unipotent pair

The actual positive and negative root-fixed subgroups are disjoint. The explicit
fixed Weyl element `w` conjugates the positive subgroup to the negative one,
and the Bruhat decomposition puts every conjugate disjoint from the positive
subgroup in the double coset `N(U) w N(U)`. An automorphism preserving `U` sends
the negative subgroup to the conjugate of `U` by `a(w)`. This conjugate remains
disjoint from `U`, so the double-coset factorization supplies an element of
`N(U)` that corrects the automorphism on both subgroups simultaneously.

The conditional reduction is retained, and the final theorem discharges both
geometric premises for every supplied `LocalBlockInput m` with `m ≥ 1`.
No simplicity, perfectness or odd-index premise is needed once the automorphism
preserves `U`. The geometry follows GLS3, Theorems 2.3.4–2.3.8,
underlying the automorphism results 2.5.1 and 2.5.12. Source:
`refs/KGroup/GLS3/chapter2.tex`; the outer-group application is in
`refs/quasithin.pdf`, printed p.510.
-/

public section
open Subgroup

private theorem map_aut_mul {G : Type*} [Group G] (H : Subgroup G) (a b : MulAut G) :
    H.map (a * b).toMonoidHom = (H.map b.toMonoidHom).map a.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem map_conj_aut {G : Type*} [Group G] (H : Subgroup G)
    (a : MulAut G) (w : G) :
    (H.map (MulAut.conj w).toMonoidHom).map a.toMonoidHom =
      (H.map a.toMonoidHom).map (MulAut.conj (a w)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

private theorem pair_adjustment {G : Type*} [Group G]
    (U V : Subgroup G) (hd : Disjoint U V) (w : G)
    (hw : U.map (MulAut.conj w).toMonoidHom = V)
    (hcell : ∀ x : G, Disjoint U (U.map (MulAut.conj x).toMonoidHom) →
      ∃ b ∈ Subgroup.normalizer U, ∃ c ∈ Subgroup.normalizer U, x = b * w * c)
    (a : MulAut G) (ha : U.map a.toMonoidHom = U) :
    ∃ g : G, U.map ((MulAut.conj g)⁻¹ * a).toMonoidHom = U ∧
      V.map ((MulAut.conj g)⁻¹ * a).toMonoidHom = V := by
  have hV : V.map a.toMonoidHom = U.map (MulAut.conj (a w)).toMonoidHom := by
    rw [← hw, map_conj_aut, ha]
  have hx : Disjoint U (U.map (MulAut.conj (a w)).toMonoidHom) := by
    rw [← hV, ← ha]
    apply disjoint_iff.mpr
    rw [← Subgroup.map_inf _ _ _ a.injective, disjoint_iff.mp hd, Subgroup.map_bot]
  obtain ⟨b, hb, c, hc, hbc⟩ := hcell (a w) hx
  have hb' : U.map (MulAut.conj b).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hb
  have hc' : U.map (MulAut.conj c).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hc
  have hVb : V.map a.toMonoidHom = V.map (MulAut.conj b).toMonoidHom := by
    rw [hV, hbc, map_mul, map_mul, map_aut_mul, map_aut_mul, hc', hw]
  refine ⟨b, ?_, ?_⟩
  · rw [map_aut_mul, ha]
    conv_lhs => rw [← hb']
    rw [← map_aut_mul, inv_mul_cancel]
    exact Subgroup.map_id U
  · rw [map_aut_mul, hVb, ← map_aut_mul, inv_mul_cancel]
    exact Subgroup.map_id V

namespace ReeF4.LocalBlockInput

/-- Simultaneous normalization, conditional on a fixed opposition representative
and the longest Bruhat double-coset criterion. Both geometric hypotheses must be
proved for the supplied `d` before using this as source-theorem assembly. -/
theorem exists_inner_adjustment_preserving_pair_of_opposition_cell
    {m : ℕ} (d : LocalBlockInput m) (w : d.fixedGroup)
    (hw : (LargeLocalSeeds.standardUnipotent d).map (MulAut.conj w).toMonoidHom =
      oppositeUnipotent d)
    (hcell : ∀ x : d.fixedGroup,
      Disjoint (LargeLocalSeeds.standardUnipotent d)
        ((LargeLocalSeeds.standardUnipotent d).map (MulAut.conj x).toMonoidHom) →
      ∃ b ∈ Subgroup.normalizer (LargeLocalSeeds.standardUnipotent d),
      ∃ c ∈ Subgroup.normalizer (LargeLocalSeeds.standardUnipotent d), x = b * w * c)
    (a : MulAut d.fixedGroup)
    (ha : (LargeLocalSeeds.standardUnipotent d).map a.toMonoidHom =
      LargeLocalSeeds.standardUnipotent d) :
    ∃ g : d.fixedGroup, PreservesUnipotentPair d ((MulAut.conj g)⁻¹ * a) :=
  pair_adjustment (LargeLocalSeeds.standardUnipotent d) (oppositeUnipotent d)
    (PairNormalization.standardUnipotent_disjoint_opposite d) w hw hcell a ha

/-- An automorphism preserving the positive fixed subgroup can be adjusted by
an inner automorphism to preserve its actual negative opposite as well.
The fixed Weyl representative and opposition-cell criterion discharge all
geometric premises; simplicity, perfectness and odd index are not needed. -/
theorem exists_inner_adjustment_preserving_pair
    {m : ℕ} (hm : 1 ≤ m) (d : LocalBlockInput m)
    (a : MulAut d.fixedGroup)
    (ha : (LargeLocalSeeds.standardUnipotent d).map a.toMonoidHom =
      LargeLocalSeeds.standardUnipotent d) :
    ∃ g : d.fixedGroup, PreservesUnipotentPair d ((MulAut.conj g)⁻¹ * a) := by
  obtain ⟨w, hw⟩ := PairNormalization.exists_opposition d
  exact exists_inner_adjustment_preserving_pair_of_opposition_cell d w hw
    (PairNormalization.OppositionCell.exists_normalizer_factors_of_disjoint hm d w hw) a ha

end ReeF4.LocalBlockInput
end
