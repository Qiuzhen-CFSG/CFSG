module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.LocalData
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.CommutatorCheck.Soundness
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.CommutatorCheck.Pairs0
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.CommutatorCheck.Pairs1
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.CommutatorCheck.Pairs2

/-!
# The fixed-involution J₂ commutator implication

For every one of the 1920 × 315 published word products `y`, the two
identities `y³ = 1` and `(t*y)⁷ = 1` imply `(t*y*t*y⁻¹)⁴ = 1`.
The proof exhausts these products with bounded kernel-checked Boolean
certificates. Accelerated permutation tables are proved equal to the
original carrier words in `Comparison`; `Soundness` translates the point
checks back to group identities. No coverage theorem is assumed here.

Source: the retained ATLAS `J2G1-p100B0` permutations. This finite implication
supplies the exclusion step in the parent first-generator fusion argument
motivated by the involution classes in GLS3, Table 5.3g; it does not by itself
claim the table's full classification or centralizer structure.
-/

public section
namespace Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion

private theorem commutator_blocks (k : Fin 60) :
    CommutatorCheck.checkRange CommutatorCheck.rowCheck (k.val * 32) 32 = true := by
  by_cases h0 : k.val < 20
  · simpa only [Nat.add_zero] using CommutatorCheck.pairs_part0 ⟨k.val, h0⟩
  by_cases h1 : k.val < 40
  · have hk : k.val - 20 < 20 := by omega
    have he : k.val - 20 + 20 = k.val := by omega
    simpa only [he] using CommutatorCheck.pairs_part1 ⟨k.val - 20, hk⟩
  · have hk : k.val - 40 < 20 := by omega
    have he : k.val - 40 + 40 = k.val := by omega
    simpa only [he] using CommutatorCheck.pairs_part2 ⟨k.val - 40, hk⟩

/-- The unconditional finite implication on the published J₂ words. -/
theorem commutator_four_on_representatives : ∀ (i : Fin 1920) (j : Fin 315),
    pairRepresentative i j ^ 3 = 1 →
    (t * pairRepresentative i j) ^ 7 = 1 →
    (t * pairRepresentative i j * t * (pairRepresentative i j)⁻¹) ^ 4 = 1 := by
  intro i j
  apply CommutatorCheck.checkPair_sound i j
  exact (CommutatorCheck.checkFin_iff _).mp
    (CommutatorCheck.all_of_blocks CommutatorCheck.rowCheck commutator_blocks i) j

end Sporadic.LeechRelated.J2.GeneratorPair.FirstFusion
