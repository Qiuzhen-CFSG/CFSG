module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.SourceData
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.Contracts
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.Witnesses
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.UnipotentClasses
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.InversionCoverage.BinaryRootNormalization
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.FixedBruhat
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.FixedGeometryTransport

/-!
# Binary inversion witnesses from the two Ree root calculations

The positive subgroup is Sylow by the existing fixed-Bruhat theorem.
Sylow conjugacy therefore reduces all involutions to that subgroup.
Root coverage and binary root normalization then identify the involution
with a conjugate of the literal subfield image of s₁ or s₄. The explicit
order-five and order-thirteen witnesses supply the required inverted element.

The proved positive-coordinate conjugacies and binary root normalization
discharge both geometric calculations for m ≥ 1, giving unconditional
`BinaryOddInversionCoverage`. The conditional assembly remains available.

Source: Guralnick--Malle, *Classification of 2F-modules, II*, Lemma 8.8,
internal p.57; GLS3, Table 2.4 and section 2.4, for the root conventions.
-/

public section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage
open Subgroup EvenInvolutionGeometry Parabolics

theorem root_coverage_of_unipotent {m : ℕ} (hU : UnipotentRootCoverage m)
    (t : Model m) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    IsLongRootInvolution t ∨ IsShortRootInvolution t := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf t = 2 := orderOf_eq_prime ht2 ht
  have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ho, pow_one])
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hindex : Odd (unipotent m).index :=
    OuterLocal.LargeAutomorphisms.unipotent_index_odd_of_standard
      (canonicalLocalBlockInput m)
      (LargeLocalSeeds.FixedBruhat.standardUnipotent_index_odd (canonicalLocalBlockInput m))
  let P := sylowOfOddIndex m hindex
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model m) Q P
  have hmap : (Q : Subgroup (Model m)).map (MulAut.conj g).toMonoidHom = unipotent m := by
    have h := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
    exact h.trans (sylowOfOddIndex_coe m hindex)
  have hmem : MulAut.conj g t ∈ unipotent m := by
    rw [← hmap]
    exact ⟨t, hQ (mem_zpowers t), rfl⟩
  have hne : MulAut.conj g t ≠ 1 := by
    intro h
    apply ht
    apply (MulAut.conj g).injective
    simpa only [map_one] using h
  have hsq : MulAut.conj g t ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hc : IsConj t (MulAut.conj g t) := isConj_iff.mpr ⟨g, rfl⟩
  rcases hU _ hmem hne hsq with ⟨a, ha, he⟩ | ⟨a, ha, he⟩
  · exact Or.inl ⟨a, ha, he.trans hc.symm⟩
  · exact Or.inr ⟨a, ha, he.trans hc.symm⟩

theorem mapped_conjugate_inversion {G H : Type*} [Group G] [Group H]
    (f : G →* H) {s x : G} (hx : s * x * s⁻¹ = x⁻¹)
    {t : H} (ht : IsConj (f s) t) :
    ∃ c : H, t * (c * f x * c⁻¹) * t⁻¹ = (c * f x * c⁻¹)⁻¹ := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp ht
  refine ⟨c, ?_⟩
  have h := congrArg ((MulAut.conj c).toMonoidHom.comp f) hx
  simpa only [map_mul, map_inv, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply] using h

/-- The literal source inversion conclusion, conditional only on the two
root calculations specified in `Contracts`. The odd-element witnesses and
positive-subgroup Sylow property are discharged here. -/
theorem binaryOddInversionCoverage_of_root_calculations {m : ℕ}
    (hU : UnipotentRootCoverage m) (hN : BinaryRootNormalization m) :
    BinaryOddInversionCoverage m := by
  intro t ht ht2
  obtain ⟨e⟩ := Subfield.nonempty_coefficientHom (k := 0) (m := m) (by simp)
  rcases root_coverage_of_unipotent hU t ht ht2 with ⟨a, ha, hc⟩ | ⟨a, ha, hc⟩
  · obtain ⟨c, hinv⟩ := mapped_conjugate_inversion (Subfield.reeMap (by simp) e)
      binaryFive_inverted ((hN e a ha).1.trans hc)
    exact ⟨e, binaryFive, c, Or.inl binaryFive_order, hinv⟩
  · obtain ⟨c, hinv⟩ := mapped_conjugate_inversion (Subfield.reeMap (by simp) e)
      binaryThirteen_inverted ((hN e a ha).2.trans hc)
    exact ⟨e, binaryThirteen, c, Or.inr binaryThirteen_order, hinv⟩

/-- Every nonidentity involution in the large Ree model inverts a conjugate
of a literal binary-subfield element of order five or thirteen. Positive
root coverage and binary normalization are both discharged. -/
theorem binaryOddInversionCoverage (m : ℕ) (hm : 1 ≤ m) :
    BinaryOddInversionCoverage m :=
  binaryOddInversionCoverage_of_root_calculations
    (unipotentRootCoverage m hm) (binaryRootNormalization m hm)

end ReeF4.FixedSpaceEstimate.BasicInvolutions.InversionCoverage
