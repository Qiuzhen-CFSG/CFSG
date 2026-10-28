module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicFixedNormalizer
public import Theory.GroupTheory.NormalizedSupCard
/-!
# An abelian five-root subgroup in the proper-centralizer branch

The elementary normal closure has order at least 32 and lies in the
center of the five-root subgroup J of order 128. Its three odd roots are
central once the fixed-subgroup centralizer is identified with J.

For either remaining root A of order four, Cartan irreducibility makes
A intersect Z(J) either in A or trivially. In the latter case, the order
bound forces J = Z(J) A, which is abelian because A is abelian. Thus both
remaining roots are central and J is abelian.

Source: Fong--Seitz I (1973), (6G), printed p.50, five-root and normalizer
argument. This gives an alternate input to its remaining root-commutator
contradiction in the index-sixteen branch; it does not yet exclude that
branch. The original pair and Chapter 12 consumers are in
LinearPairCubicNormalizerSource and LinearPairCubicNormalizerChapter12.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- A large central normal closure and the actual Cartan actions force all
five roots to commute in the proper-centralizer alternative. -/
theorem binary_middleFive_abelian_of_fixed_centralizer
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μj : localGroup Q split j ≃* PSL(2,F))
    (hi : Nat.card (simpleRoot Q split i) = 2)
    (hj : Nat.card (simpleRoot Q split j) = 4)
    (hCJ : middleRootCentralizer Q split i j = middleFive Q split i j)
    (hJM : middleFive Q split i j ≤ centralizer (fixedOddRoots Q split i j : Set (X ⧸ Q.D))) :
    IsMulCommutative (middleFive Q split i j) := by
  let J := middleFive Q split i j
  let Z := J ⊓ centralizer (J : Set (X ⧸ Q.D))
  let H := Q.tits.B ⊓ Q.tits.N
  let M := fixedOddRoots Q split i j
  have hJcard : Nat.card J = 128 := by
    rw [middleFive_card Q split hm i j hij,hi,hj]; norm_num
  have hJC : J ≤ middleRootCentralizer Q split i j := hCJ.ge
  have hEZ := middleRootClosure_le_middle_center Q split hm i j hij hKj hJC
  have hi16 : (middleRootCentralizer Q split i j).relIndex (simpleRemainder Q split i) = 16 := by
    rw [hCJ]
    exact binary_middleFive_quotient_card Q split hm i j hij hi hj
  have hZcard : 32 ≤ Nat.card Z :=
    ((binary_middleRootClosure_card_bounds Q split hm i j hij hKj hi hj hJC).2.2 hi16).trans
      (card_le_of_le hEZ)
  have hSup (A B : Subgroup (X ⧸ Q.D)) (hA : H ≤ normalizer (A : Set (X ⧸ Q.D)))
      (hB : H ≤ normalizer (B : Set (X ⧸ Q.D))) : H ≤ normalizer ((A ⊔ B : Subgroup _) : Set _) :=
    (le_inf hA hB).trans (normalizer_inf_normalizer_le_normalizer_sup A B)
  have hHJ : H ≤ normalizer (J : Set (X ⧸ Q.D)) :=
    hSup _ _ (hSup _ _ (hSup _ _ (hSup _ _
      (rootAt_torus_normalizes Q split i _) (rootAt_torus_normalizes Q split j _))
      (rootAt_torus_normalizes Q split i _)) (rootAt_torus_normalizes Q split j _))
      (rootAt_torus_normalizes Q split i _)
  have hHZ : H ≤ normalizer (Z : Set (X ⧸ Q.D)) :=
    (le_inf hHJ (hHJ.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf
  have hroot (w : Weyl Q) (hAJ : rootAt Q split j w ≤ J) :
      rootAt Q split j w ≤ centralizer (J : Set (X ⧸ Q.D)) := by
    let A := rootAt Q split j w
    have hAcard : Nat.card A = 4 := by
      simpa only [A,rootAt,card_rightConjugate] using hj
    have hAA : ⁅A,A⁆ = ⊥ := by
      have hh := congrArg (fun D => rightConjugate D (representative w : X ⧸ Q.D))
        (simpleRoot_commutator_eq_bot_of_linear Q split j μj)
      simpa only [A,rootAt,rightConjugate,comap_equiv_eq_map_symm',map_commutator,Subgroup.map_bot] using hh
    let : IsMulCommutative A := commutator_self_eq_bot_iff.mp hAA
    by_cases hne : Z ⊓ A = ⊥
    · have hZA : Z ≤ centralizer (A : Set (X ⧸ Q.D)) :=
        inf_le_right.trans (centralizer_le hAJ)
      have he : Z ⊔ A = J := eq_of_le_of_card_ge (sup_le inf_le_left hAJ) (by
        rw [card_sup_eq_mul_of_normalizes_of_disjoint Z A
          ((le_centralizer_iff.mp hZA).trans (Subgroup.centralizer_le_normalizer _))
          (disjoint_iff.mpr hne),hAcard,hJcard]
        omega)
      apply le_centralizer_iff.mpr
      rw [←he]
      exact sup_le hZA A.le_centralizer
    · have he := QuadrangleStructure.rootAt_eq_of_torus_invariant Q split j μj hKj w
        (Z ⊓ A) inf_le_right hne
        ((le_inf hHZ (rootAt_torus_normalizes Q split j w)).trans
          inf_normalizer_le_normalizer_inf)
      have hAZ : rootAt Q split j w ≤ Z := he ▸ (inf_le_left : Z ⊓ A ≤ Z)
      exact hAZ.trans inf_le_right
  have hB := hroot (Q.simple i*Q.simple j)
    (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right)))
  have hD := hroot (Q.simple i*Q.simple j*Q.simple i)
    (le_sup_of_le_left le_sup_right)
  have hM : M ≤ centralizer (J : Set (X ⧸ Q.D)) := le_centralizer_iff.mp hJM
  apply le_centralizer_iff_isMulCommutative.mp
  have he : J = M ⊔ rootAt Q split j (Q.simple i*Q.simple j) ⊔
      rootAt Q split j (Q.simple i*Q.simple j*Q.simple i) := by
    dsimp only [J,M,middleFive,fixedOddRoots]
    ac_rfl
  change J ≤ centralizer (J : Set (X ⧸ Q.D))
  nth_rw 1 [he]
  exact sup_le (sup_le hM hB) hD
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
