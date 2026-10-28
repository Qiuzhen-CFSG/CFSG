module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Scalar

/-!
# The tetrahedral difference operator on the binary Leech space

Choose an explicit double transposition in the literal four-point scalar group.
Its product with the published three-cycle is conjugate to that three-cycle.
The existing scalar quadratic identity therefore implies
`Y (u - 1) = (u - 1) Y⁻¹` on the full binary Leech space. Consequently the
kernel of `u - 1` is stable under Y and is fixed by all three involutions of U.
It is exactly the literal U-fixed space, with no dimension or frame premise.

The integral negative-square lift then identifies this kernel with the image
of `u - 1`. This is the geometric input for descending the ambient polar form
in `Pairing.BinaryDescent`; its scalar balance uses the same intertwining identity.

Source context: Aschbacher, *Sporadic Groups* (1994), 49.2, p.280, and the
natural-plus-dual action in 49.5, p.283. The imported icosian scalar and Leech
models retain the ATLAS attribution in their source modules and LICENSES/ATLAS.txt.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Algebra Atlas.Codes Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel.PairingGeometry

abbrev A4 := alternatingGroup fourPoints

def invol : A4 :=
  ⟨Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩ *
    Equiv.swap ⟨2, by decide⟩ ⟨3, by decide⟩, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
def conj : A4 :=
  ⟨Equiv.swap ⟨0, by decide⟩ ⟨2, by decide⟩ *
    Equiv.swap ⟨1, by decide⟩ ⟨3, by decide⟩, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

theorem invol_mem : invol ∈ alternatingGroup.kleinFour fourPoints := by
  apply Subgroup.subset_closure
  change invol.val.cycleType = {2, 2}
  decide +kernel
theorem invol_ne_one : invol ≠ 1 := by decide +kernel
theorem invol_sq : invol * invol = 1 := by decide +kernel
theorem mixed_conj : conj * threeCycle * conj⁻¹ = threeCycle * invol := by decide +kernel

theorem klein_cases (a : A4) (ha : a ∈ alternatingGroup.kleinFour fourPoints) :
    a = 1 ∨ a = invol ∨ a = threeCycle * invol * threeCycle⁻¹ ∨
      a = threeCycle⁻¹ * invol * threeCycle := by
  have hh : a = 1 ∨ a.val.cycleType = {2, 2} := by
    simpa only [← SetLike.mem_coe, alternatingGroup.coe_kleinFour_of_card_eq_four fourPoints_card,
      Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] using ha
  simp only [Subtype.ext_iff] at hh ⊢
  exact (by decide +kernel : ∀ p : Equiv.Perm fourPoints,
    p = 1 ∨ p.cycleType = {2, 2} →
      p = 1 ∨ p = invol.val ∨ p = (threeCycle * invol * threeCycle⁻¹).val ∨
        p = (threeCycle⁻¹ * invol * threeCycle).val) a.val hh

abbrev u : LeechCentralQuotient := scalarFour invol
abbrev rho := quotientModTwoRepresentation

theorem u_mem : u ∈ U := ⟨invol, invol_mem, rfl⟩
theorem u_sq : u * u = 1 := by rw [← map_mul, invol_sq, map_one]
theorem u_ne_one : u ≠ 1 := by
  intro h
  exact invol_ne_one (scalarFour_injective (h.trans (map_one scalarFour).symm))

theorem mixed_polynomial (v : LeechModTwo) :
    rho (y * u) (rho (y * u) v) + rho (y * u) v + v = 0 := by
  have he : y * u = scalarFour conj * y * (scalarFour conj)⁻¹ := by
    simpa only [map_mul, map_inv, y] using (congrArg scalarFour mixed_conj).symm
  rw [he]
  have h := congrArg (rho (scalarFour conj))
    (Long.y_polynomial (rho (scalarFour conj)⁻¹ v))
  simpa only [map_add, map_zero, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
    LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] using h

theorem y_inverse_sum (v : LeechModTwo) : rho y v + rho y⁻¹ v = v := by
  have h := Long.y_polynomial (rho y⁻¹ v)
  simp only [map_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at h
  have hz : v + v = 0 := by simpa using (two_smul Bit v).symm
  have hn : -v = v := (eq_neg_iff_add_eq_zero.mpr hz).symm
  calc
    rho y v + rho y⁻¹ v = -v := eq_neg_of_add_eq_zero_left (by rwa [add_right_comm] at h)
    _ = v := hn

theorem mixed_inverse_sum (v : LeechModTwo) :
    rho (y * u) v + rho (y * u)⁻¹ v = v := by
  have h := mixed_polynomial (rho (y * u)⁻¹ v)
  simp only [map_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at h
  have hz : v + v = 0 := by simpa using (two_smul Bit v).symm
  have hn : -v = v := (eq_neg_iff_add_eq_zero.mpr hz).symm
  exact (eq_neg_of_add_eq_zero_left (by rwa [add_right_comm] at h)).trans hn

theorem intertwine (v : LeechModTwo) :
    rho y (difference u v) = difference u (rho y⁻¹ v) := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_left u_sq
  have h := mixed_inverse_sum v
  rw [_root_.mul_inv_rev, huinv, map_mul, map_mul] at h
  change rho y (rho u v) + rho u (rho y⁻¹ v) = v at h
  have hy := y_inverse_sum v
  change rho y (rho u v - v) = rho u (rho y⁻¹ v) - rho y⁻¹ v
  rw [map_sub]
  have hn (w : LeechModTwo) : -w = w := by
    have hz : w + w = 0 := by simpa using (two_smul Bit w).symm
    exact (eq_neg_iff_add_eq_zero.mpr hz).symm
  have he := eq_sub_of_add_eq (h.trans hy.symm)
  rw [he]
  calc
    ((rho y v + rho y⁻¹ v) - rho u (rho y⁻¹ v)) - rho y v =
        rho y⁻¹ v - rho u (rho y⁻¹ v) := by abel
    _ = rho u (rho y⁻¹ v) - rho y⁻¹ v := by
      rw [sub_eq_add_neg, sub_eq_add_neg, hn, hn, add_comm]


theorem fixedSpace_eq_kernel : fixedSpace = LinearMap.ker (difference u) := by
  apply le_antisymm
  · intro v hv
    exact sub_eq_zero.mpr (hv u u_mem)
  · intro v hv
    have hD : difference u v = 0 := hv
    have hinv : difference u (rho y⁻¹ v) = 0 := by
      rw [← intertwine, hD, map_zero]
    have hy : difference u (rho y v) = 0 := by
      have h := congrArg (difference u) (y_inverse_sum v)
      rw [map_add, hD, hinv, add_zero] at h
      exact h
    have hfix : rho u v = v := sub_eq_zero.mp hD
    have hfixinv : rho u (rho y⁻¹ v) = rho y⁻¹ v := sub_eq_zero.mp hinv
    have hfixy : rho u (rho y v) = rho y v := sub_eq_zero.mp hy
    rintro z ⟨a, ha, rfl⟩
    rcases klein_cases a ha with rfl | rfl | rfl | rfl
    · simp only [map_one, LinearEquiv.coe_one, id_eq]
    · exact hfix
    · have h : rho y (rho u (rho y⁻¹ v)) = v := by
        rw [hfixinv, map_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
      simpa only [map_mul, map_inv, LinearEquiv.mul_apply, y] using h
    · have h : rho y⁻¹ (rho u (rho y v)) = v := by
        rw [hfixy, map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
      simpa only [map_mul, map_inv, LinearEquiv.mul_apply, y] using h

theorem range_eq_fixedSpace : LinearMap.range (difference u) = fixedSpace := by
  obtain ⟨g, hg, hg2⟩ := U_involution_lift ⟨u, u_mem⟩ u_ne_one
  change leechCentralProjection g = u at hg
  rw [← hg, difference_range_eq_ker g hg2, hg, fixedSpace_eq_kernel]


theorem fixedSpace_finrank_eq_twelve : Module.finrank Bit fixedSpace = 12 := by
  rw [fixedSpace_eq_kernel]
  exact U_involution_fixed_finrank ⟨u, u_mem⟩ u_ne_one

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel.PairingGeometry
