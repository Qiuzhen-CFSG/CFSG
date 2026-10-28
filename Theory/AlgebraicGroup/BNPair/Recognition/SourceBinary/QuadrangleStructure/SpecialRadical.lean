module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.RootCommutators
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.RootCommutators

/-!
# The special quadrangle radical and its crossed-root center

If the opposite simple root is abelian, the radical's derived subgroup
lies in the other radical. Its invariance under its own reflection puts
it in the intersection of two radicals, the literal crossed root.
If the radical's center lies in its derived subgroup, that center is
therefore exactly the intrinsic center of the crossed root: the other
two root factors commute with it. The center-side opposite commutator
cannot vanish, since otherwise the nontrivial simple root would lie in
that center and hence in its own disjoint complementary section.

DGS (11.8)(f) supplies the specialness premise for the beta radical.
No assumption that the nonabelian root is elementary is made. These
statements locate the beta Frattini/center layer and prove the nonzero
part of Fong--Seitz I (6A)(c); equality of that commutator with the whole
center still needs its source scalar-action argument.

Source: DGS (11.8)(f), p.176; Fong--Seitz I (3G), (6A)(c), pp.37--38.
-/

public noncomputable section
open Subgroup
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem commutator_conjugate (A B : Subgroup (X ⧸ Q.D)) (n : X ⧸ Q.D) :
    rightConjugate ⁅A,B⁆ n = ⁅rightConjugate A n,rightConjugate B n⁆ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]

/-- An abelian opposite simple root puts the radical's whole derived subgroup
inside the crossed root, even when that crossed root is nonabelian. -/
theorem remainder_derived_le_cross_root (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥) :
    ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ ≤ rootAt Q split j (Q.simple i) := by
  let n := representative (Q.simple j)
  have hn : (n : X ⧸ Q.D) ∈ Q.tits.standardParabolic {Q.simple j} :=
    Q.tits.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton _)
      (Q.tits.representative_mem_bruhatCell _ n (representative_spec _))
  have hd := (commutator_mono (show simpleRemainder Q split j ≤ split.U from inf_le_left)
    (show simpleRemainder Q split j ≤ split.U from inf_le_left)).trans
      (unipotent_commutator_le_remainder Q split i hVi hA)
  have hfix : rightConjugate ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆
      (n : X ⧸ Q.D) = ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ := by
    rw [commutator_conjugate,rightConjugate_eq_self _
      (remainder_parabolic_normalizes Q split j hVj hn)]
  rw [← remainder_conjugate_intersection Q split hm j i hij.symm n (representative_spec _)]
  refine le_inf hd ?_
  rw [← hfix]
  exact comap_mono hd

/-- The special radical's center is exactly the intrinsic center of the
intervening nonabelian root, embedded in the same quotient. -/
theorem remainder_center_eq_cross_center (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    (hZ : (center (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype ≤
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆) :
    (center (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype =
      (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype := by
  let V := simpleRemainder Q split j
  let C := rootAt Q split j (Q.simple i)
  have hCV : C ≤ V := cross_root_le_own_remainder Q split hm j i hij.symm
  apply le_antisymm
  · rintro x ⟨v,hv,rfl⟩
    have hvc := (hZ.trans (remainder_derived_le_cross_root Q split hm i j hij hVi hVj hA))
      (mem_map_of_mem V.subtype hv)
    refine ⟨⟨v,hvc⟩,mem_center_iff.mpr (fun c => ?_),rfl⟩
    apply Subtype.ext
    exact congrArg (fun t : simpleRemainder Q split j => (t : X ⧸ Q.D))
      (mem_center_iff.mp hv ⟨c,hCV c.property⟩)
  · rintro x ⟨c,hc,rfl⟩
    have hcen : V ≤ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) := by
      dsimp only [V]
      rw [remainder_eq_three_roots Q split hm j i hij.symm]
      apply sup_le (sup_le ?_ ?_) ?_
      · intro a ha
        apply mem_centralizer_singleton_iff.mpr
        exact (mem_centralizer_iff.mp
          (commutator_eq_bot_iff_le_centralizer.mp
            (adjacent_roots_commute Q split hm i j hij hVi hVj) ha) c c.property).symm
      · intro a ha
        apply mem_centralizer_singleton_iff.mpr
        exact congrArg Subtype.val (mem_center_iff.mp hc ⟨a,ha⟩)
      · intro a ha
        apply mem_centralizer_singleton_iff.mpr
        exact mem_centralizer_iff.mp
          (commutator_eq_bot_iff_le_centralizer.mp
            (middle_roots_commute Q split hm i j hij hVi hVj) ha) c c.property |>.symm
    refine ⟨⟨c,hCV c.property⟩,mem_center_iff.mpr (fun v => ?_),rfl⟩
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hcen v.property))

/-- Specialness of the beta radical excludes a zero center-side commutator. -/
theorem cross_root_commutator_ne_bot_of_special_radical (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    (hZ : (center (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype ≤
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ ≠ ⊥ := by
  intro hz
  have hcen : simpleRoot Q split i ≤ centralizer (simpleRemainder Q split j : Set (X ⧸ Q.D)) := by
    apply le_centralizer_iff.mpr
    rw [remainder_eq_three_roots Q split hm j i hij.symm]
    exact sup_le (sup_le
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hA))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (adjacent_roots_commute Q split hm i j hij hVi hVj))))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz))
  have hAC : simpleRoot Q split i ≤
      (center (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype := by
    intro a ha
    refine ⟨⟨a,(opposite_roots_le_remainder Q split i j hij).1 ha⟩,
      mem_center_iff.mpr (fun v => ?_),rfl⟩
    exact Subtype.ext (mem_centralizer_iff.mp (hcen ha) v v.property)
  have hAV : simpleRoot Q split i ≤ simpleRemainder Q split i :=
    (hAC.trans hZ).trans ((commutator_mono (show simpleRemainder Q split j ≤ split.U from inf_le_left)
      (show simpleRemainder Q split j ≤ split.U from inf_le_left)).trans
        (unipotent_commutator_le_remainder Q split i hVi hA))
  exact simpleRoot_ne_bot Q split i ((inf_eq_left.mpr hAV).symm.trans
    (disjoint_iff.mp (simpleRoot_disjoint_remainder Q split i)))
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
