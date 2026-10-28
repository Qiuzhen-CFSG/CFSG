module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.Marking
public import Theory.AtlasPort.OtherSporadic.Conway.DerivedCrossTransitivity

/-!
# Reducing negative-square Leech fusion to signed Golay permutations

An isometry squaring to central negation generates a group of order four.
The odd number of Leech crosses gives a fixed cross. Transitivity on crosses
then conjugates the isometry into the literal Golay monomial subgroup,
preserving its square. This reduces the required ambient conjugacy to a
finite signed-permutation problem without assuming a Conway class theorem.

The square equation forces the coordinate permutation to be a fixed-point-free
involution, with opposite signs on each pair. These equations supply the
input for the remaining monomial conjugacy calculation. The final theorem
here only transfers that calculation; it does not assert its premise.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5,
pp.283–284, and the root-four conventions on p.269. Cross transitivity,
monomial recovery and the literal Leech actions are existing attributed ATLAS
ports; no new ATLAS source is copied here.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion

theorem exists_fixedCross_of_square_negation (g : LeechIsometryGroup)
    (hg : g ^ 2 = negationIsometry) : ∃ X : LeechCross, crossAction g X = X := by
  let Z := Subgroup.zpowers g
  let : MulAction Z LeechCross :=
    MulAction.compHom LeechCross (crossRepresentation.comp Z.subtype)
  have hZ : IsPGroup 2 Z := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_zpowers, order_four_of_sq_negation hg]
    norm_num)
  obtain ⟨X, hX⟩ := hZ.nonempty_fixed_point_of_prime_not_dvd_card LeechCross (by
    rw [leechCross_card]
    decide)
  exact ⟨X, MulAction.mem_fixedPoints.mp hX ⟨g, Subgroup.mem_zpowers g⟩⟩

theorem exists_monomial_of_square_negation (g : LeechIsometryGroup)
    (hg : g ^ 2 = negationIsometry) :
    ∃ m : GolayMonomialGroup, (monomialEmbedding m) ^ 2 = negationIsometry ∧
      IsConj g (monomialEmbedding m) := by
  obtain ⟨X, hX⟩ := exists_fixedCross_of_square_negation g hg
  let _ := full_cross_transitive
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq LeechIsometryGroup standardCross X
  change crossAction s standardCross = X at hs
  let k := s⁻¹ * g * s
  have hkX : crossAction k standardCross = standardCross := by
    rw [show k = s⁻¹ * (g * s) by dsimp [k]; group]
    rw [crossAction_mul, crossAction_mul, hs, hX, ← hs, ← crossAction_mul,
      inv_mul_cancel]
    rfl
  let m := recoverMonomial k hkX
  have hm : monomialEmbedding m = k := recoverMonomial_spec k hkX
  refine ⟨m, ?_, isConj_iff.mpr ⟨s⁻¹, by simpa [k] using hm.symm⟩⟩
  rw [hm]
  calc
    k ^ 2 = s⁻¹ * g ^ 2 * s := by dsimp [k]; simp only [pow_two]; group
    _ = negationIsometry := by
      rw [hg, Subgroup.mem_center_iff.mp negation_mem_center s⁻¹]
      simp [mul_assoc]

theorem monomial_square_negation_parameters (m : GolayMonomialGroup)
    (hm : (monomialEmbedding m) ^ 2 = negationIsometry) :
    Function.Involutive m.right.val.symm ∧
      (∀ i, m.left.toAdd.val (m.right.val.symm i) = m.left.toAdd.val i + 1) ∧
      ∀ i, m.right.val.symm i ≠ i := by
  have hs : m * m = monomialCentralElement := monomialEmbedding_injective (by
    rw [map_mul, monomialCentralElement_image]
    exact hm)
  have hp : Function.Involutive m.right.val.symm := by
    intro i
    exact congrArg (fun n : GolayMonomialGroup => n.right.val.symm i) hs
  have hc (i : Omega) : m.left.toAdd.val (m.right.val.symm i) = m.left.toAdd.val i + 1 := by
    have he := congrArg (fun n : GolayMonomialGroup => n.left.toAdd.val i) hs
    change m.left.toAdd.val i + m.left.toAdd.val (m.right.val.symm i) = 1 at he
    rcases bit_cases (m.left.toAdd.val i) with hi | hi <;>
      rcases bit_cases (m.left.toAdd.val (m.right.val.symm i)) with hj | hj <;> simp_all
  refine ⟨hp, hc, ?_⟩
  intro i hi
  have he := hc i
  rw [hi] at he
  have hz : (0 : Bit) = 1 := add_left_cancel (by simpa only [add_zero] using he)
  exact zero_ne_one hz

theorem projection_isConj_scalar_of_monomial
    (hmono : ∀ m : GolayMonomialGroup,
      (monomialEmbedding m) ^ 2 = negationIsometry →
      IsConj (leechCentralProjection (monomialEmbedding m)) scalarInvolution)
    (g : LeechIsometryGroup) (hg : g ^ 2 = negationIsometry) :
    IsConj (leechCentralProjection g) scalarInvolution := by
  obtain ⟨m, hm, hc⟩ := exists_monomial_of_square_negation g hg
  exact (leechCentralProjection.map_isConj hc).trans (hmono m hm)

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion
