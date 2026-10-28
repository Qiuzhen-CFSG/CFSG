module
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.EightSylow
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.SpecificGroups.SymmetricEight.CentralPair
/-!
# The Sylow-fixed line of the alternating eight-point natural module

Four even binary-tree permutations force every representative to be constant
on the two four-point blocks. Modulo the constant word there are just two
vectors. Sylow conjugacy preserves this uniqueness for every Sylow subgroup.

Source: Aschbacher--Smith B.3.1--2, pp.83--84; the seed in 15.1.28, p.1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricEight
open A6ShadowTwoLocals CentralPair
namespace BinaryPermutation

private def lineFixer : Fin 4 → S8 :=
  ![treeGenerator 0 * treeGenerator 1, treeGenerator 4,
    treeGenerator 2 * treeGenerator 3, treeGenerator 5]
private theorem lineFixer_even : ∀ i, Equiv.Perm.sign (lineFixer i) = 1 := by decide
private theorem lineFixer_tree (i : Fin 4) : lineFixer i ∈ treeGroup := by
  fin_cases i
  · exact treeGroup.mul_mem (treeGenerator_mem 0) (treeGenerator_mem 1)
  · exact treeGenerator_mem 4
  · exact treeGroup.mul_mem (treeGenerator_mem 2) (treeGenerator_mem 3)
  · exact treeGenerator_mem 5
private theorem lineFixer_fixed : ∀ j, ∃ i : Fin 8, lineFixer j i = i := by decide

private def halfWord : Full (Fin 8) := ![1,1,1,1,0,0,0,0]
private def halfVector : natural (Fin 8) :=
  ⟨(constants (Fin 8)).mkQ halfWord, halfWord, by change (∑ i, halfWord i) = 0; decide, rfl⟩

private theorem tree_natural_fixed_two (v : natural (Fin 8))
    (hv : v ∈ fixedSpace (alternatingNaturalRepresentation (Fin 8)) evenTreeSylow) :
    v = 0 ∨ v = halfVector := by
  obtain ⟨w,hw,hrep⟩ := v.property
  have he (j : Fin 4) : representation (Fin 8) (lineFixer j) w = w := by
    obtain ⟨i,hi⟩ := lineFixer_fixed j
    apply (deleted_fixed_iff_of_fixed_point _ w i hi).mp
    rw [hrep]
    exact congrArg (fun z : natural (Fin 8) => z.val) (hv ⟨⟨lineFixer j,show lineFixer j ∈ alternatingGroup (Fin 8) from lineFixer_even j⟩, by
      change (⟨lineFixer j,show lineFixer j ∈ alternatingGroup (Fin 8) from lineFixer_even j⟩ : A8) ∈ (evenTreeSylow : Subgroup A8)
      rw [evenTreeSylow_coe]
      exact lineFixer_tree j⟩)
  have h01 := congrFun (he 0) 0
  have h23 := congrFun (he 0) 2
  have h02 := congrFun (he 1) 0
  have h45 := congrFun (he 2) 4
  have h67 := congrFun (he 2) 6
  have h46 := congrFun (he 3) 4
  change w 1 = w 0 at h01
  change w 3 = w 2 at h23
  change w 2 = w 0 at h02
  change w 5 = w 4 at h45
  change w 7 = w 6 at h67
  change w 6 = w 4 at h46
  have hcoords (i : Fin 8) : w i = if i.val < 4 then w 0 else w 4 := by
    fin_cases i <;> simp_all
  by_cases hsame : w 0 = w 4
  · left
    apply Subtype.ext
    change v.val = 0
    rw [← hrep]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact (mem_constants_iff w).mpr ⟨w 0,fun i => by rw [hcoords i,hsame]; split_ifs <;> rfl⟩
  · right
    apply Subtype.ext
    change v.val = (constants (Fin 8)).mkQ halfWord
    rw [← hrep]
    apply (Submodule.Quotient.eq _).mpr
    refine (mem_constants_iff _).mpr ⟨w 4, fun i => ?_⟩
    have hsub : w 0 - 1 = w 4 := (by decide : ∀ a b : ZMod 2, a ≠ b → a - 1 = b) _ _ hsame
    change w i - halfWord i = w 4
    rw [hcoords i]
    fin_cases i <;> simp [halfWord, hsub]

/-- A Sylow two-subgroup of A8 fixes at most one nonzero natural vector. -/
theorem alternatingEight_sylow_fixed_unique (Q : Sylow 2 A8)
    (v w : natural (Fin 8)) (hv : v ≠ 0)
    (hfv : v ∈ fixedSpace (alternatingNaturalRepresentation (Fin 8)) Q)
    (hfw : w ∈ fixedSpace (alternatingNaturalRepresentation (Fin 8)) Q) :
    w = 0 ∨ w = v := by
  let ρ := alternatingNaturalRepresentation (Fin 8)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A8 Q evenTreeSylow
  have hmap : (Q : Subgroup A8).map (MulAut.conj g).toMonoidHom = evenTreeSylow := by
    change ((g • Q : Sylow 2 A8) : Subgroup A8) = _
    rw [hg]
  have transported (z : natural (Fin 8)) (hz : z ∈ fixedSpace ρ Q) :
      ρ g z ∈ fixedSpace ρ evenTreeSylow := by
    intro a
    have ha : (a : A8) ∈ (Q : Subgroup A8).map (MulAut.conj g).toMonoidHom :=
      hmap.symm ▸ a.property
    obtain ⟨x,hx,he⟩ := ha
    change ρ a.val (ρ g z) = ρ g z
    rw [← he]
    change ρ (g*x*g⁻¹) (ρ g z) = ρ g z
    have hm : (g*x*g⁻¹)*g = g*x := by group
    rw [← Module.End.mul_apply, ← map_mul, hm, map_mul, Module.End.mul_apply]
    exact congrArg (ρ g) (hz ⟨x,hx⟩)
  have hvg := transported v hfv
  have hwg := transported w hfw
  have hi := (ρ.apply_bijective g).1
  have hvn : ρ g v ≠ 0 := fun hz => hv (hi (hz.trans (map_zero _).symm))
  have hvh := (tree_natural_fixed_two _ hvg).resolve_left hvn
  rcases tree_natural_fixed_two _ hwg with hz | he
  · exact Or.inl (hi (hz.trans (map_zero _).symm))
  · exact Or.inr (hi (he.trans hvh.symm))
end BinaryPermutation
