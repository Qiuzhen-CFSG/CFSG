module
public import Theory.Representation.BinarySevenCode.PermutationAction
public import Theory.Representation.BinaryPermutation.SevenParabolic.Geometry

/-!
# Constant-weight-four geometry on seven letters

The nonzero singular vectors of the even-word quadratic form have weight four.
Polarization makes every constant-weight-four subspace totally isotropic, so its
rank is at most three. A rank-three space equals its orthogonal complement;
if two coordinate evaluations agreed there, their weight-two pair vector would
belong to the same space. Thus every such space separates the seven coordinates
and has trivial pointwise permutation stabilizer.

This treats every simplex space, without choosing a conjugacy representative.
It repairs the linear input to Aschbacher--Smith, 12.3.9--10, printed p.810;
it does not claim that an ambient simplex centralizer normalizes the full module.
-/

@[expose] public section
namespace BinarySevenCode
open Module
open BinaryPermutation.SevenParabolic (Space pairing)

/-- Weight-four spaces are totally isotropic for the dot product. -/
theorem weight_four_isotropic (U : Submodule (ZMod 2) Space)
    (hw : ∀ v ∈ U, v ≠ 0 → weight v.val = 4) :
    ∀ v ∈ U, ∀ w ∈ U, pairing v w = 0 := by
  have hq (v : Space) (hv : v ∈ U) : BinaryPermutation.SevenParabolic.form v = 0 := by
    apply (BinaryPermutation.SevenParabolic.singular_iff v).mpr
    by_cases hz : v = 0
    · exact Or.inl hz
    · exact Or.inr (hw v hv hz)
  intro v hv w hwU
  have ha := BinaryPermutation.SevenParabolic.form_add v w
  rw [hq v hv, hq w hwU, hq (v + w) (U.add_mem hv hwU), zero_add, zero_add] at ha
  exact ha.symm

theorem finrank_le_three_of_weight_four (U : Submodule (ZMod 2) Space)
    (hw : ∀ v ∈ U, v ≠ 0 → weight v.val = 4) : finrank (ZMod 2) U ≤ 3 :=
  BinaryPermutation.SevenParabolic.isotropic_finrank_le U (weight_four_isotropic U hw)

theorem orthogonal_eq_of_weight_four_rank_three (U : Submodule (ZMod 2) Space)
    (hw : ∀ v ∈ U, v ≠ 0 → weight v.val = 4) (hd : finrank (ZMod 2) U = 3) :
    pairing.orthogonal U = U := by
  have hle : U ≤ pairing.orthogonal U := by
    intro v hv w hwU
    exact weight_four_isotropic U hw w hwU v hv
  apply (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [LinearMap.BilinForm.finrank_orthogonal
    BinaryPermutation.SevenParabolic.pairing_nondegenerate,
    BinaryPermutation.SevenParabolic.finrank_space, hd]

/-- A three-dimensional constant-weight-four code separates the seven letters. -/
theorem coordinates_separated_of_weight_four_rank_three
    (U : Submodule (ZMod 2) Space)
    (hw : ∀ v ∈ U, v ≠ 0 → weight v.val = 4) (hd : finrank (ZMod 2) U = 3)
    (i j : Fin 7) (hij : ∀ v ∈ U, v.val i = v.val j) : i = j := by
  by_contra hne
  let p : Space := ⟨Pi.single i 1 + Pi.single j 1, by
    simp [BinaryPermutation.mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]⟩
  have hp : p ∈ pairing.orthogonal U := by
    intro v hv
    change dotProduct v.val (Pi.single i 1 + Pi.single j 1) = 0
    simp only [dotProduct_add, dotProduct_single, mul_one, hij v hv]
    exact CharTwo.add_self_eq_zero _
  rw [orthogonal_eq_of_weight_four_rank_three U hw hd] at hp
  have hpne : p ≠ 0 := by
    intro he
    have he' := congrArg (fun v : Space => v.val i) he
    simp [p, hne] at he'
  have hpw : weight p.val = 2 := by
    have he : (Finset.univ.filter (fun k => p.val k ≠ 0)) = {i, j} := by
      ext k
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        simp_all [p, Pi.single_apply, eq_comm]
    rw [weight, he, Finset.card_pair hne]
  have := hw p hp hpne
  omega

theorem perm_eq_one_of_fixes_weight_four_rank_three
    (U : Submodule (ZMod 2) Space)
    (hw : ∀ v ∈ U, v ≠ 0 → weight v.val = 4) (hd : finrank (ZMod 2) U = 3)
    (p : Equiv.Perm (Fin 7)) (hp : ∀ v ∈ U, ∀ i, v.val (p i) = v.val i) : p = 1 := by
  apply Equiv.ext
  intro i
  exact coordinates_separated_of_weight_four_rank_three U hw hd (p i) i
    (fun v hv => hp v hv i)

end BinarySevenCode
