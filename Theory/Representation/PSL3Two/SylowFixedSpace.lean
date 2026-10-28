module

public import Theory.Representation.BinarySylowFixedSpace
public import Theory.Representation.PSL3Two.ParabolicCyclic.Seed

/-!
# Cubic witnesses on the binary natural three-space

The upper triangular Sylow fixes the first coordinate line. The matrix
with lower block [[0,1],[1,1]] fixes that line and has order three.
For the contragredient, reuse the checked line-parabolic calculation.
Sylow conjugacy gives witnesses for every Sylow subgroup, and the same
witness acts on two identically marked summands.

The actual actor is SL₃(2), canonically isomorphic to PSL₃(2) by
`Matrix.PSL3Two.equiv`. These are the model calculations used with
Aschbacher–Smith B.4.8, B.5.1(1)(ii), and B.5.6 in Lemma 15.4.18,
printed pp.91,99,105,1163. No natural-plus-dual sum is included.
-/

@[expose] public section

open Representation Representation.BinaryOffender Representation.BinarySylowFixedSpace Matrix
namespace BinaryLinearThree.SylowFixedSpace
open FanoDecomposition ParabolicCyclic

private def pointCycle : Group := ⟨!![1,0,0;0,0,1;0,1,1], by decide⟩

private theorem pointCycle_fixes : ∀ v : Vector,
    W (Matrix.PSL3Two.Bruhat.upper 1) v = v →
    W (Matrix.PSL3Two.Bruhat.upper 4) v = v → W pointCycle v = v := by
  decide +kernel

/-- An explicit point-parabolic cubic fixes the natural Sylow fixed line. -/
theorem exists_cubic_fixer_natural (S : Sylow 2 Group) :
    ∃ d : Group, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace W (S : Subgroup Group), W d v = v := by
  apply sylow_fixedSpace_enlargement_of_cubic W (flagSylow : Subgroup Group)
    flagSylow.isPGroup' pointCycle (by decide) (by decide) _ S
  intro v hv
  rw [flagSylow_coe, markedFlag_stabilizer] at hv
  exact pointCycle_fixes v (hv ⟨_, Matrix.PSL3Two.Bruhat.upper_mem 1⟩)
    (hv ⟨_, Matrix.PSL3Two.Bruhat.upper_mem 4⟩)

/-- The line-parabolic cubic supplies the contragredient calculation. -/
theorem exists_cubic_fixer_dual (S : Sylow 2 Group) :
    ∃ d : Group, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace W.dual (S : Subgroup Group), W.dual d v = v := by
  apply sylow_fixedSpace_enlargement_of_cubic W.dual (flagSylow : Subgroup Group)
    flagSylow.isPGroup' lineCycle lineCycle_cube (by decide) _ S
  intro v hv
  rw [flagSylow_coe, markedFlag_stabilizer] at hv
  exact borel_fixed_dual_cycle_fixed v (fun g hg => hv ⟨g, hg⟩)

/-- Both natural summands have the same marking and the same cubic fixer. -/
theorem exists_cubic_fixer_doubled_natural (S : Sylow 2 Group) :
    ∃ d : Group, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace (W.prod W) (S : Subgroup Group), (W.prod W) d v = v := by
  obtain ⟨d, hd, hc, hf⟩ := exists_cubic_fixer_natural S
  exact ⟨d, hd, hc, fixes_prod W W _ hf hf⟩

/-- The identical statement for two copies of the actual linear dual. -/
theorem exists_cubic_fixer_doubled_dual (S : Sylow 2 Group) :
    ∃ d : Group, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace (W.dual.prod W.dual) (S : Subgroup Group),
        (W.dual.prod W.dual) d v = v := by
  obtain ⟨d, hd, hc, hf⟩ := exists_cubic_fixer_dual S
  exact ⟨d, hd, hc, fixes_prod W.dual W.dual _ hf hf⟩

end BinaryLinearThree.SylowFixedSpace
