module

public import Theory.SpecificGroups.Suzuki.DerangementOrders
public import Theory.SpecificGroups.Suzuki.SplitNormalizerGeometry

/-!
# Suzuki local structure from the ovoid action

This module collects the geometric local inputs to Huppert--Blackburn,
*Finite Groups III*, XI.3.10(b),(e),(g), pp. 191--192, and XI.3.12(e).
All subgroups are the concrete subgroups of `SuzukiMatrixGroup m`.

Root regularity gives `suzukiRootSubgroup_normalizer` and
`suzukiRootSubgroup_conjugates_disjoint`. The two fixed points of a nonidentity
split-torus element give `suzukiSplitTorus_conjugates_disjoint` and identify its
normalizer with their setwise stabilizer (`suzukiSplitTorus_normalizer`). The
explicit `suzukiWeyl` has order two and acts by inversion; the torus and its
Weyl coset give `suzukiSplitTorus_normalizer_card` and
`suzukiSplitTorus_normalizer_dihedral`.

The Frobenius action of the Borel covers every element with a fixed point by
root or split-torus conjugates. The remaining elements act freely together
with every nonidentity power, so their orders divide the ovoid degree `q² + 1`.
The same argument for commuting elements gives
`suzukiMatrixGroup_centralizer_card_dvd`. Below we assemble these results into
coverage statements using subgroup conjugates. No nonsplit torus or subgroup
classification is needed.
-/

namespace BenderSuzuki.MatrixGroups

/-- Fixed-point elements are precisely those in conjugates of the root group
or the split torus. -/
public theorem suzukiOvoid_fixed_point_iff_mem_conjugate (m : ℕ) (hm : 0 < m)
    (x : SuzukiMatrixGroup m) :
    (∃ a : SuzukiOvoid m, x • a = a) ↔
      ∃ k : SuzukiMatrixGroup m,
        x ∈ (SuzukiRootSubgroup m).map (MulAut.conj k).toMonoidHom ∨
        x ∈ (SuzukiSplitTorus m).map (MulAut.conj k).toMonoidHom := by
  constructor
  · intro hx
    obtain ⟨k, hk | hk⟩ := suzukiOvoid_fixed_point_coverage m hm x hx
    · exact ⟨k, Or.inl ⟨k⁻¹ * x * k, hk, by simp [MulAut.conj_apply, mul_assoc]⟩⟩
    · exact ⟨k, Or.inr ⟨k⁻¹ * x * k, hk, by simp [MulAut.conj_apply, mul_assoc]⟩⟩
  · rintro ⟨k, hx | hx⟩
    · obtain ⟨r, hr, rfl⟩ := hx
      refine ⟨k • suzukiOvoidInfinity m, ?_⟩
      change (k * r * k⁻¹) • (k • suzukiOvoidInfinity m) = k • suzukiOvoidInfinity m
      simp only [mul_smul, inv_smul_smul,
        suzukiRootSubgroup_fix_infinity m hm r hr]
    · obtain ⟨t, ht, rfl⟩ := hx
      refine ⟨k • suzukiOvoidInfinity m, ?_⟩
      change (k * t * k⁻¹) • (k • suzukiOvoidInfinity m) = k • suzukiOvoidInfinity m
      simp only [mul_smul, inv_smul_smul,
        ((mem_suzukiSplitTorus_iff_fix_pair m t).mp ht).1]

/-- Every element lies in a root conjugate, lies in a split-torus conjugate,
or is a derangement of order dividing `q² + 1`. -/
public theorem suzukiOvoid_element_coverage (m : ℕ) (hm : 0 < m)
    (x : SuzukiMatrixGroup m) :
    (∃ k : SuzukiMatrixGroup m,
      x ∈ (SuzukiRootSubgroup m).map (MulAut.conj k).toMonoidHom) ∨
    (∃ k : SuzukiMatrixGroup m,
      x ∈ (SuzukiSplitTorus m).map (MulAut.conj k).toMonoidHom) ∨
    ((∀ a : SuzukiOvoid m, x • a ≠ a) ∧
      orderOf x ∣ (2 ^ (2 * m + 1)) ^ 2 + 1) := by
  by_cases hx : ∃ a : SuzukiOvoid m, x • a = a
  · obtain ⟨k, hk | hk⟩ := (suzukiOvoid_fixed_point_iff_mem_conjugate m hm x).mp hx
    · exact Or.inl ⟨k, hk⟩
    · exact Or.inr (Or.inl ⟨k, hk⟩)
  · have hd : ∀ a : SuzukiOvoid m, x • a ≠ a := fun a ha => hx ⟨a, ha⟩
    exact Or.inr (Or.inr ⟨hd, suzukiOvoid_derangement_order_dvd m hm x hd⟩)

end BenderSuzuki.MatrixGroups
