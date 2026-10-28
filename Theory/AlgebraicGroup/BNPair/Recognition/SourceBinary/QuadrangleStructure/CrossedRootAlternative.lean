module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.TorusIrreducibility

/-!
# Choosing a commuting side in a linear split quadrangle

Cartan irreducibility makes any nonzero same-type crossed-root
commutator the entire intervening root. That root is then the derived
subgroup of the complementary radical and is normalized by its whole
parabolic. The opposite commutator lies both in this root and in the
other middle root. Reflection and root disjointness force it to vanish.

Thus at least one side commutes, with no field-size or perfectness
restriction. LinearRecognition uses this alternative to select the
orientation of the full symplectic comparison when the root orders agree.
The unequal-field U₄ branch keeps its already established orientation.

Source: Fong--Seitz I (6A), the equal-linear paragraph on p.37,
using (3G) and (5C). All roots and relative normalizers belong to the
same marked split quotient; no exhaustive row disjunction is assumed.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- One of the two same-type crossed-root commutators vanishes. -/
theorem linear_cross_root_alternative {F k : Type*}
    [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split i ≃* PSL(2,F))
    (ν : localGroup Q split j ≃* PSL(2,k)) :
    ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = ⊥ ∨
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ = ⊥ := by
  by_cases hz : ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = ⊥
  · exact Or.inl hz
  right
  have hcross := cross_root_commutator_eq_of_nonzero Q split hm i j hij hVi hVj μ hz
  have hderived := (remainder_derived_frattini Q split hm i j hij hVi hVj
    (simpleRoot_elementary_of_linear Q split i μ)
    (simpleRoot_elementary_of_linear Q split j ν)).1.trans hcross
  have hn : Q.tits.standardParabolic {Q.simple i} ≤
      normalizer (rootAt Q split i (Q.simple j) : Set (X ⧸ Q.D)) := by
    rw [←hderived]
    intro a ha
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (remainder_parabolic_normalizes Q split i hVi ha)]
  have hle : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ ≤
      rootAt Q split i (Q.simple j) :=
    le_normalizer_iff_commutator_le_right.mp
      ((simpleRoot_le Q split i).trans
        (split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans hn)))
  by_contra hz'
  have he := cross_root_commutator_eq_of_nonzero Q split hm j i hij.symm hVj hVi ν hz'
  rw [he] at hle
  let n := representative (Q.simple i)
  have hconj := comap_mono (f := (MulAut.conj (n : X ⧸ Q.D)).toMonoidHom) hle
  change rightConjugate (rootAt Q split j (Q.simple i)) (n : X ⧸ Q.D) ≤
    rightConjugate (rootAt Q split i (Q.simple j)) (n : X ⧸ Q.D) at hconj
  have hs : Q.simple i * Q.simple i = 1 := by
    simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2
  rw [rootAt_right Q split j (Q.simple i) (Q.simple i) n (representative_spec _),hs,
    rootAt_one,cross_root_reflection_fixed Q split hm i j hij n (representative_spec _)] at hconj
  have hbad : simpleRoot Q split j ≤ simpleRemainder Q split j :=
    hconj.trans (opposite_roots_le_remainder Q split i j hij).2
  exact simpleRoot_ne_bot Q split j ((inf_eq_left.mpr hbad).symm.trans
    (disjoint_iff.mp (simpleRoot_disjoint_remainder Q split j)))
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
