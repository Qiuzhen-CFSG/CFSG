module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.Generation.Words
public import Theory.AtlasPort.LinearGroups.G2.Generation

/-!
# The explicit octonion pair generates G₂(3)

The matrix word certificates supply each root at parameter one, both Weyl
maps, and the two torus elements with parameter two. Additivity supplies all
three root parameters. Since two generates the units of the prime field, the
two torus certificates supply the full split torus. The existing singular
vector reduction theorem `Atlas.G2.generated_eq_top` finishes the proof.

Sources: the certified words in `Generation/Words.lean`, and the
ATLAS octonion generation proof in `Theory.AtlasPort.LinearGroups.G2.Generation`.
See `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison
open Generation

private theorem additive_mem {G : Type*} [Group G] (H : Subgroup G)
    (f : ZMod 3 → G) (hadd : ∀ a b, f a * f b = f (a+b)) (h1 : f 1 ∈ H)
    (a : ZMod 3) : f a ∈ H := by
  have h2 : f 2 ∈ H := by
    simpa only [hadd, show (1:ZMod 3)+1=2 by decide] using H.mul_mem h1 h1
  have h0 : f 0 ∈ H := by
    simpa only [hadd, show (2:ZMod 3)+1=0 by decide] using H.mul_mem h2 h1
  fin_cases a <;> assumption

private theorem unit_pow_two (u : (ZMod 3)ˣ) :
    ∃ n : Fin 2, twoUnit ^ (n : Nat) = u := by
  revert u
  decide

private theorem torus_mem (l m : (ZMod 3)ˣ) : torus l m ∈ pairClosure := by
  obtain ⟨i, rfl⟩ := unit_pow_two l
  obtain ⟨j, rfl⟩ := unit_pow_two m
  have hi := pairClosure.pow_mem torus_two_one_mem (i : Nat)
  have hj := pairClosure.pow_mem torus_one_two_mem (j : Nat)
  have he : torus (twoUnit ^ (i : Nat)) (twoUnit ^ (j : Nat)) =
      torus twoUnit 1 ^ (i : Nat) * torus 1 twoUnit ^ (j : Nat) := by
    calc
      _ = torusHom ((twoUnit, 1) ^ (i : Nat) * (1, twoUnit) ^ (j : Nat)) := by
        simp only [Prod.pow_mk, Prod.mk_mul_mk, one_pow, mul_one, one_mul]
        rfl
      _ = _ := by rw [map_mul, map_pow, map_pow]; rfl
  rw [he]
  exact pairClosure.mul_mem hi hj

/-- The fixed pair of octonion automorphisms generates the full group. -/
theorem closure_generator_range : Subgroup.closure (Set.range generator) = ⊤ := by
  have hu : unipotent (K := ZMod 3) ≤ pairClosure := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with (((((hg|hg)|hg)|hg)|hg)|hg)
    all_goals obtain ⟨a,rfl⟩ := hg
    · exact additive_mem _ _ rootA_add rootA_one_mem a
    · exact additive_mem _ _ rootB_add rootB_one_mem a
    · exact additive_mem _ _ rootC_add rootC_one_mem a
    · exact additive_mem _ _ rootD_add rootD_one_mem a
    · exact additive_mem _ _ rootE_add rootE_one_mem a
    · exact additive_mem _ _ rootF_add rootF_one_mem a
  have hrw : rootWeylSubgroup (K := ZMod 3) ≤ pairClosure := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with hg | hg
    · exact hu hg
    · rcases hg with rfl | hg
      · exact weylR_mem
      · obtain rfl := Set.mem_singleton_iff.mp hg
        exact weylS_mem
  have ht : splitTorus (K := ZMod 3) ≤ pairClosure := by
    rintro g ⟨⟨l,m⟩, rfl⟩
    exact torus_mem l m
  change pairClosure = ⊤
  apply top_unique
  rw [← generated_eq_top]
  exact sup_le hrw ht

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison
