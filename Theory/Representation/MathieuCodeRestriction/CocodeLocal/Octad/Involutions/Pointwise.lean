module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Involutions.Representatives
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Pointwise centralizer of the octad involution fixed space

Weight-two cocode classes have unique pair representatives. Fixing the
involution's fixed space pointwise therefore preserves every invariant pair.
Pairs inside its fixed octad force pointwise octad fixation, and its pair
{6,7} restricts the image of point 6 to two choices. The established native
heptad rigidity theorem, transferred through the point embedding, then makes
the actor either the identity or the given involution.

This is the pointwise centralizer in Aschbacher–Smith H.15.2(5), printed
pp.398–399. The proof does not replace it with a setwise stabilizer.
-/

public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry Representation.BinaryOffender
open scoped Pointwise
namespace MathieuCode.CocodeOctad.Involutions
noncomputable section

private lemma seed_fixer_eq_one (g : M24)
    (hg : ∀ i ∈ LinearFourCore.seedOctad.val, g • i = i)
    (h6 : g • (6 : Fin 24) = 6) : g = 1 := by
  have h0 := hg 0 ((LinearFourCore.mem_seedOctad 0).mpr (Or.inl rfl))
  have hr : g ∈ pointEmbedding.range := by
    rw [pointEmbedding_range]
    exact h0
  obtain ⟨u, rfl⟩ := hr
  have hu : u = 1 := by
    refine M23Geometry.heptad_fixer_eq_one_of_fix_complement u ?_ 6 (by decide +kernel) ?_
    · intro j hj
      apply m23PointEmbedding.injective
      change m23PointEmbedding (u.val j) = m23PointEmbedding j
      rw [← pointEmbedding_apply]
      exact hg _ ((LinearFourCore.mem_seedOctad _).mpr (Or.inr ⟨j, hj, rfl⟩))
    · apply m23PointEmbedding.injective
      change m23PointEmbedding (u.val 6) = m23PointEmbedding 6
      rw [← pointEmbedding_apply]
      rw [show m23PointEmbedding (6 : Fin 23) = (6 : Fin 24) from by decide +kernel]
      exact h6
  rw [hu, map_one]

private lemma centralizer_preserves_pair (g : M24)
    (hg : g ∈ subspaceKernel cocodeRepresentation
      (fixedSpace cocodeRepresentation (Subgroup.zpowers z)) ⊤)
    (a b : Fin 24) (hab : a ≠ b)
    (hz : z • ({a,b} : Finset (Fin 24)) = {a,b}) :
    g • a = a ∨ g • a = b := by
  let P : PointPair := ⟨{a,b}, by simp [hab]⟩
  have hv : pairVector P ∈ fixedSpace cocodeRepresentation (Subgroup.zpowers z) :=
    (mem_fixedSpace_zpowers_iff _ _ _).mpr ((pairVector_fixed_iff z P).mpr hz)
  have hp := (pairVector_fixed_iff g P).mp (hg.2 _ hv)
  have hm : g • a ∈ g • P.val := Finset.smul_mem_smul_finset (by simp [P])
  rw [hp] at hm
  simpa [P] using hm

private lemma centralizer_fixes_seed (g : M24)
    (hg : g ∈ subspaceKernel cocodeRepresentation
      (fixedSpace cocodeRepresentation (Subgroup.zpowers z)) ⊤) :
    ∀ i ∈ LinearFourCore.seedOctad.val, g • i = i := by
  have hp (a b : Fin 24) (hab : a ≠ b) (ha : z • a = a) (hb : z • b = b) :
      g • a = a ∨ g • a = b := by
    apply centralizer_preserves_pair g hg a b hab
    simp [Finset.smul_finset_def, ha, hb]
  have h0 : g • (0 : Fin 24) = 0 := by
    have h1 := hp 0 1 (by decide) (by decide +kernel) (by decide +kernel)
    have h2 := hp 0 2 (by decide) (by decide +kernel) (by decide +kernel)
    rcases h1 with h1 | h1
    · exact h1
    · rcases h2 with h2 | h2
      · exact h2
      · exact False.elim ((by decide : (1 : Fin 24) ≠ 2) (h1.symm.trans h2))
  have hfix : ∀ i ∈ LinearFourCore.seedOctad.val, g • i = i := by
    intro i hi
    by_cases hi0 : i = 0
    · simpa [hi0] using h0
    · rcases hp i 0 hi0 ((z_fixed_iff i).mpr hi) (by decide +kernel) with h | h
      · exact h
      · exact False.elim (hi0 ((MulAction.injective g) (h.trans h0.symm)))
  exact hfix

lemma pointwiseCentralizer_z :
    subspaceKernel cocodeRepresentation
      (fixedSpace cocodeRepresentation (Subgroup.zpowers z)) ⊤ = Subgroup.zpowers z := by
  apply le_antisymm
  · intro g hg
    have hfix := centralizer_fixes_seed g hg
    have h6 := centralizer_preserves_pair g hg 6 7 (by decide) (by decide +kernel)
    rcases h6 with h6 | h6
    · rw [seed_fixer_eq_one g hfix h6]
      exact Subgroup.one_mem _
    · have he : z⁻¹ * g = 1 := by
        apply seed_fixer_eq_one
        · intro i hi
          rw [mul_smul, hfix i hi, inv_smul_eq_iff]
          exact ((z_fixed_iff i).mpr hi).symm
        · rw [mul_smul, h6]
          decide +kernel
      have he' : g = z := (inv_mul_eq_one.mp he).symm
      rw [he']
      exact Subgroup.mem_zpowers z
  · intro g hg
    exact ⟨Subgroup.mem_top _, fun _ hv => hv ⟨g, hg⟩⟩



end
end MathieuCode.CocodeOctad.Involutions
