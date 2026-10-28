module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.TorusIrreducibility
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.QuadraticLinear

/-!
# The original quadratic-linear branch without a derived-order assumption

DGS (11.3)(e) gives a nonzero derived subgroup of the original beta
core. The marked core transport and the three-root radical calculation
identify its image with the opposite-root commutator. Cartan irreducibility
in the actual small linear local group then gives equality with the
crossed root, removing the derived-order premise of QuadraticLinear.
The elementary alpha core supplies the other commuting clause and its
order q^4; the embedded Frattini identity and full S order are retained.

The same theorem applies to an independent geometric marking; the literal
original quotient application uses originalMarkedIso and the same Q.q.
Both orientations and q=2 are included. The local PSL2 marking and the
section 2/5 kernel containments remain genuine earlier transport inputs.
The full root-generated actor identification and irreducible radical action
are separate remaining obligations, as are both U5 equalities.

Source: DGS (11.3)(e), (11.5)--(11.7), pp.169--175;
Fong--Seitz I (6A)(b), pp.37--38. Final source assembly retains the
original profile and generic local-transport producers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  {F : Type*} [Field F] [Finite F] [CharP F 2]

include e h in
/-- The nonzero original core-derived subgroup fills the actual crossed root.
The linear marking belongs to the genuine source local permutation group. -/
theorem marked_cross_root_commutator_eq_of_nonzero_derived
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split i ≃* PSL(2,F))
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hQj : letI := original_core_normal_in_sylow (L := L) (S := S) j
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S j).pCoreIn 2).subgroupOf S))
    (hne : ⁅(parabolic L S i).pCoreIn 2,(parabolic L S i).pCoreIn 2⁆ ≠ ⊥) :
    ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = rootAt Q split i (Q.simple j) := by
  apply Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.cross_root_commutator_eq_of_nonzero
    Q split hm i j hij hVi hVj μ
  intro hz
  have hder := (Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.remainder_derived_frattini
    Q split hm i j hij hVi hVj
    (marked_simpleRoot_elementary_of_original_quotient Q e h split i hVi hQi)
    (marked_simpleRoot_elementary_of_original_quotient Q e h split j hVj hQj)).1
  have hc := marked_remainder_derived_card Q e h split i hVi
  rw [hder,hz,card_bot] at hc
  exact hne (card_eq_one.mp hc.symm)

include e h in
/-- The general U4 commutator and Frattini conclusions use the nonzero
clause of DGS (11.3)(e), with no derived-order premise. -/
theorem marked_quadratic_linear_roots_of_nonzero_derived
    (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j) (q : ℕ) (hq : 0 < q)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* PSL(2,F))
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = q^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = q + 1)
    (helem : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2))
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hQj : letI := original_core_normal_in_sylow (L := L) (S := S) j
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S j).pCoreIn 2).subgroupOf S))
    (hne : ⁅(parabolic L S j).pCoreIn 2,(parabolic L S j).pCoreIn 2⁆ ≠ ⊥) :
    Nat.card (simpleRoot Q split i) = q^2 ∧
      Nat.card (simpleRoot Q split j) = q ∧
      IsElementaryAbelian 2 (simpleRemainder Q split i) ∧
      Nat.card (simpleRemainder Q split i) = q^4 ∧
      ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = ⊥ ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ = rootAt Q split j (Q.simple i) ∧
      (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype =
        rootAt Q split j (Q.simple i) ∧
      Nat.card S = q^6 := by
  have hcross := marked_cross_root_commutator_eq_of_nonzero_derived Q e h split hm j i hij.symm
    hVj hVi μ hQj hQi hne
  have hder := (Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.remainder_derived_frattini
    Q split hm j i hij.symm hVj hVi
    (marked_simpleRoot_elementary_of_original_quotient Q e h split j hVj hQj)
    (marked_simpleRoot_elementary_of_original_quotient Q e h split i hVi hQi)).1
  have hcard : Nat.card (⁅(parabolic L S j).pCoreIn 2,
      (parabolic L S j).pCoreIn 2⁆ : Subgroup G) = q := by
    rw [← marked_remainder_derived_card Q e h split j hVj,hder,hcross,rootAt,card_rightConjugate]
    have hidx := marked_commonBorel_root_index Q e h split j
    omega
  exact marked_quadratic_linear_roots Q e h split hm i j hij q hq hVi hVj
    hindexi hindexj helem hQi hQj hcard

include h in
omit Q e split in
/-- The same U4 conclusion on the literal original quotient, with the full
original S image and both endpoint markings unchanged. -/
theorem original_quadratic_linear_commutators_of_nonzero_derived
    (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hm : rotationOrder Q₀ = 4)
    (i j : Fin 2) (hij : i ≠ j) (q : ℕ) (hq : 0 < q)
    (hVi : simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
    (hVj : simpleRemainder Q₀ split₀ j ≤ localKernel Q₀ j)
    (μ : localGroup Q₀ split₀ j ≃* PSL(2,F))
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = q^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = q + 1)
    (helem : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2))
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hQj : letI := original_core_normal_in_sylow (L := L) (S := S) j
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S j).pCoreIn 2).subgroupOf S))
    (hne : ⁅(parabolic L S j).pCoreIn 2,(parabolic L S j).pCoreIn 2⁆ ≠ ⊥) :
    ⁅simpleRoot Q₀ split₀ j,rootAt Q₀ split₀ j (Q₀.simple i)⁆ = ⊥ ∧
      ⁅simpleRoot Q₀ split₀ i,rootAt Q₀ split₀ i (Q₀.simple j)⁆ = rootAt Q₀ split₀ j (Q₀.simple i) ∧
      Nat.card ((S.subgroupOf (generated L S)).map Q₀.q) = q^6 := by
  obtain ⟨hri,hrj,hR,hRc,hcomm,hcross,hPhi,hS⟩ := marked_quadratic_linear_roots_of_nonzero_derived
    Q₀ (originalMarkedIso Q₀) h split₀ hm i j hij q hq hVi hVj μ hindexi hindexj helem hQi hQj hne
  refine ⟨hcomm,hcross,?_⟩
  rw [quotient_sourceS_image_eq_unipotent h Q₀ split₀]
  exact (Nat.card_congr (markedSylowEquiv Q₀ (originalMarkedIso Q₀) h split₀).toEquiv).symm.trans hS

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
