module
public import Theory.SpecificGroups.Suzuki.RootOvoidGeometry

/-!
# The remaining-point orbit of a Suzuki Sylow

For a nonbinary Suzuki group, identify each Sylow normalizer with a
point stabilizer of the natural ovoid and prove that its Sylow is
transitive on the complement of that point. Conjugate the standard root
group and its regular action together, retaining the same fixed point.

Source: Huppert--Blackburn, Finite Groups III, XI.3.3, as formalized in
RootOvoidGeometry. The application in DGS, Groups and Graphs (1985),
12.3(a), p.179, is CommutingThreeProfile.SuzukiNeighborOrbits.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace BenderSuzuki.MatrixGroups

/-- Every Sylow normalizer is the stabilizer of a point, and that Sylow
is transitive on the other points of the actual Suzuki ovoid. -/
theorem suzuki_sylow_remaining_orbit {n : ℕ} (hn : 0 < n) (T : Sylow 2 (SuzukiMatrixGroup n)) :
    ∃ p : SuzukiOvoid n, normalizer (T : Set (SuzukiMatrixGroup n)) =
      MulAction.stabilizer (SuzukiMatrixGroup n) p ∧
      ∀ a b : SuzukiOvoid n, a ≠ p → b ≠ p →
        ∃ t ∈ (T : Subgroup (SuzukiMatrixGroup n)), t • a = b := by
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow n hn
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup n) P T
  have hmap : (P : Subgroup (SuzukiMatrixGroup n)).map (MulAut.conj g).toMonoidHom = T := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨g • suzukiOvoidInfinity n, ?_, ?_⟩
  · have he := Subgroup.map_equiv_normalizer_eq (P : Subgroup (SuzukiMatrixGroup n)) (MulAut.conj g)
    rw [hmap, hP, suzukiRootSubgroup_normalizer n hn, suzukiBorelSubgroup_eq_stabilizer n hn] at he
    simp only [Sylow.coe_coe] at he
    rw [← he, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  · intro a b ha hb
    have ha' : g⁻¹ • a ≠ suzukiOvoidInfinity n := by
      intro he
      exact ha (by rw [← he, smul_inv_smul])
    have hb' : g⁻¹ • b ≠ suzukiOvoidInfinity n := by
      intro he
      exact hb (by rw [← he, smul_inv_smul])
    obtain ⟨u, he, _⟩ := suzukiRootSubgroup_regular n (g⁻¹ • a) (g⁻¹ • b) ha' hb'
    refine ⟨g * u * g⁻¹, ?_, ?_⟩
    · rw [← hmap]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom (show (u : SuzukiMatrixGroup n) ∈ (P : Subgroup (SuzukiMatrixGroup n)) by
        rw [hP]; exact u.property)
    · rw [mul_smul, mul_smul, he, smul_inv_smul]
end BenderSuzuki.MatrixGroups
