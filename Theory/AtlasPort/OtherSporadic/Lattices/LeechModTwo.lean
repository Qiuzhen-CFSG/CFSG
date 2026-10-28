/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechModTwo.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechSmallShells
public import Mathlib.Algebra.Module.ZMod

/-!
The quotient of the Leech lattice by twice itself.
Reduction in a lattice basis identifies it with the twenty-four-dimensional binary coordinate space.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes

def doubleLeech : leech →+ leech where
  toFun x := (2 : ℕ) • x
  map_zero' := by simp
  map_add' x y := nsmul_add x y 2

def twiceLeech : AddSubgroup leech := doubleLeech.range

/-- The quotient by twice the lattice, not ambient coordinate reduction. -/
abbrev LeechModTwo := leech ⧸ twiceLeech

def leechReduction : leech →+ LeechModTwo := QuotientAddGroup.mk' twiceLeech

theorem twiceLeech_mem (x : leech) : x ∈ twiceLeech ↔ ∃ y : leech, (2 : ℕ) • y = x := Iff.rfl

instance : Module Bit LeechModTwo := QuotientAddGroup.zmodModule (n := 2)
  (fun x => ⟨x,rfl⟩ : ∀ x : leech, (2 : ℕ) • x ∈ twiceLeech)

def leechBasisModTwo : leech →+ BinaryWord :=
  (coordinateMod 2).comp leechBasis.equivFun.toAddEquiv.toAddMonoidHom

theorem leechBasisModTwo_surjective : Function.Surjective leechBasisModTwo :=
  (coordinateMod_surjective 2).comp leechBasis.equivFun.surjective

theorem twiceLeech_eq_ker : twiceLeech = leechBasisModTwo.ker := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    change coordinateMod 2 (leechBasis.equivFun ((2 : ℕ) • y)) = 0
    rw [map_nsmul,map_nsmul]
    ext i
    simp
  · intro hx
    have hc : leechBasis.equivFun x ∈ (coordinateMod 2).ker := hx
    rw [← coordinateScale_range 2] at hc
    obtain ⟨y,hy⟩ := hc
    refine ⟨leechBasis.equivFun.symm y,?_⟩
    apply leechBasis.equivFun.injective
    change leechBasis.equivFun ((2 : ℕ) • leechBasis.equivFun.symm y) = _
    rw [map_nsmul,leechBasis.equivFun.apply_symm_apply]
    simpa only [coordinateScale,AddMonoidHom.coe_mk,ZeroHom.coe_mk,natCast_zsmul] using hy

def leechModTwoEquiv : LeechModTwo ≃+ BinaryWord :=
  (QuotientAddGroup.quotientAddEquivOfEq twiceLeech_eq_ker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective leechBasisModTwo leechBasisModTwo_surjective)

def leechModTwoLinearEquiv : LeechModTwo ≃ₗ[Bit] BinaryWord :=
  { leechModTwoEquiv with map_smul' := ZMod.map_smul leechModTwoEquiv }

instance : Finite LeechModTwo := Finite.of_equiv BinaryWord leechModTwoEquiv.symm

theorem leechModTwo_card : Nat.card LeechModTwo = 2 ^ 24 := by
  rw [Nat.card_congr leechModTwoEquiv.toEquiv]
  simp [Omega,HexIndex]

theorem leechModTwo_finrank : Module.finrank Bit LeechModTwo = 24 := by
  rw [leechModTwoLinearEquiv.finrank_eq]
  simp [BinaryWord,Omega,HexIndex]

theorem leechReduction_surjective : Function.Surjective leechReduction :=
  QuotientAddGroup.mk'_surjective twiceLeech

theorem leechReduction_eq_zero (x : leech) : leechReduction x = 0 ↔ ∃ y : leech, (2 : ℕ) • y = x := by
  change (QuotientAddGroup.mk x : LeechModTwo) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  rfl

end Atlas.Lattices
