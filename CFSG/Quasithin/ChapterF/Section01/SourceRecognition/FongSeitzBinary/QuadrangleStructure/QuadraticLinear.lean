module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.MarkedRadicals
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderFormulas

/-!
# Quadratic-linear quadrangle commutators from original core data

Orient i as the large-field endpoint alpha and j as the small-field
endpoint beta. The original full-Borel indices give simple-root orders
q² and q. DGS (11.7)(e), Q_alpha = Z_alpha, gives the elementary
complementary section and its q⁴ order. The original Sylow quotients from
(11.5) and the branch hypothesis of (11.7) give elementary simple roots.
The opposite commutator is identified with the transported beta-core
derived subgroup, so its order q forces the exact crossed-root equality.
The embedded Frattini subgroup and full original S order follow as well.

The general derived-order premise remains explicit: (11.3)(e) gives a
nonzero derived subgroup contained in Z_beta, not that equality by itself.
The scalar-action argument that removes this premise remains part of the
quadrangle structural proof. At q=2, the nonzero containment in the actual
center layer of order two suffices, and the binary specialization proves
the derived order internally. No perfectness is required in either case.

These statements apply to the original SourceQuotient and to an independent
geometric marking, with both full endpoint squares and the original S map
unchanged. They supply the subgroup portion of the U4 route. The full
rank-one identification and irreducible action still require proof; the
actor/tensor realization consumed by UnitarySource.FourApplication remains
with its source owner. Nothing here asserts the complete (6A)(b) theorem.
Source: DGS (11.3), (11.5)--(11.7), pp.168--175;
Fong--Seitz I (6A)(b), pp.37--38, and II (8B).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
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

include e h in
/-- Original core and quotient data give the precise quadratic-linear root structure. -/
theorem marked_quadratic_linear_roots (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j) (q : ℕ) (hq : 0 < q)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = q^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = q + 1)
    (helem : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2))
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hQj : letI := original_core_normal_in_sylow (L := L) (S := S) j
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S j).pCoreIn 2).subgroupOf S))
    (hderived : Nat.card (⁅(parabolic L S j).pCoreIn 2,
      (parabolic L S j).pCoreIn 2⁆ : Subgroup G) = q) :
    Nat.card (simpleRoot Q split i) = q^2 ∧
      Nat.card (simpleRoot Q split j) = q ∧
      IsElementaryAbelian 2 (simpleRemainder Q split i) ∧
      Nat.card (simpleRemainder Q split i) = q^4 ∧
      ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = ⊥ ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ = rootAt Q split j (Q.simple i) ∧
      (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype =
        rootAt Q split j (Q.simple i) ∧
      Nat.card S = q^6 := by
  have hri : Nat.card (simpleRoot Q split i) = q^2 := by
    have hh := marked_commonBorel_root_index Q e h split i
    omega
  have hrj : Nat.card (simpleRoot Q split j) = q := by
    have hh := marked_commonBorel_root_index Q e h split j
    omega
  have hprod : Nat.card (simpleRoot Q split 0) * Nat.card (simpleRoot Q split 1) = q^3 := by
    have hi : i = 0 ∨ i = 1 := by omega
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (hij rfl).elim
    · rw [hri,hrj]; ring
    · rw [hrj,hri]; ring
    · exact (hij rfl).elim
  have hU : Nat.card split.U = q^6 := by
    rw [unipotent_card_even Q split 2 hm,hprod]
    ring
  have hR : Nat.card (simpleRemainder Q split i) = q^4 := by
    have hc := unipotent_card_simple Q split i
    rw [hU,hri] at hc
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hq 2)
    exact hc.symm.trans (by ring)
  have hcomm := marked_cross_root_commutator_eq Q e h split hm j i hij.symm
    hVj hVi hQj hQi q hindexj hderived
  have hPhi := (Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.remainder_derived_frattini
    Q split hm j i hij.symm hVj hVi
    (marked_simpleRoot_elementary_of_original_quotient Q e h split j hVj hQj)
    (marked_simpleRoot_elementary_of_original_quotient Q e h split i hVi hQi)).2
  exact ⟨hri,hrj,marked_remainder_elementary Q e split i hVi helem,hR,
    marked_root_commutator_of_elementary_core Q e split j i hij.symm hVi helem,
    hcomm,hPhi.trans hcomm,(Nat.card_congr (markedSylowEquiv Q e h split).toEquiv).trans hU⟩

include h in
omit Q e split in
/-- Literal original-quotient application, retaining the image of the same full S. -/
theorem original_quadratic_linear_commutators
    (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    (hm : rotationOrder Q₀ = 4)
    (i j : Fin 2) (hij : i ≠ j) (q : ℕ) (hq : 0 < q)
    (hVi : simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
    (hVj : simpleRemainder Q₀ split₀ j ≤ localKernel Q₀ j)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = q^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = q + 1)
    (helem : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2))
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hQj : letI := original_core_normal_in_sylow (L := L) (S := S) j
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S j).pCoreIn 2).subgroupOf S))
    (hderived : Nat.card (⁅(parabolic L S j).pCoreIn 2,
      (parabolic L S j).pCoreIn 2⁆ : Subgroup G) = q) :
    ⁅simpleRoot Q₀ split₀ j,rootAt Q₀ split₀ j (Q₀.simple i)⁆ = ⊥ ∧
      ⁅simpleRoot Q₀ split₀ i,rootAt Q₀ split₀ i (Q₀.simple j)⁆ = rootAt Q₀ split₀ j (Q₀.simple i) ∧
      Nat.card ((S.subgroupOf (generated L S)).map Q₀.q) = q^6 := by
  obtain ⟨hri,hrj,hR,hRc,hcomm,hcross,hPhi,hS⟩ := marked_quadratic_linear_roots
    Q₀ (originalMarkedIso Q₀) h split₀ hm i j hij q hq hVi hVj hindexi hindexj helem hQi hQj hderived
  refine ⟨hcomm,hcross,?_⟩
  rw [quotient_sourceS_image_eq_unipotent h Q₀ split₀]
  exact (Nat.card_congr (markedSylowEquiv Q₀ (originalMarkedIso Q₀) h split₀).toEquiv).symm.trans hS
include e h in
/-- At q=2 the source nonzero derived layer inside the center of order two
already gives the exact required commutator; no derived-order premise remains. -/
theorem marked_binary_quadratic_linear_roots (hm : rotationOrder Q = 4)
    (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = 5)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = 3)
    (helem : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2))
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hQj : letI := original_core_normal_in_sylow (L := L) (S := S) j
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S j).pCoreIn 2).subgroupOf S))
    (Z : Subgroup G) (hZ : Nat.card Z = 2)
    (hbound : ⁅(parabolic L S j).pCoreIn 2,(parabolic L S j).pCoreIn 2⁆ ≤ Z)
    (hnonzero : ⁅(parabolic L S j).pCoreIn 2,(parabolic L S j).pCoreIn 2⁆ ≠ ⊥) :
    Nat.card (simpleRoot Q split i) = 4 ∧
      Nat.card (simpleRoot Q split j) = 2 ∧
      IsElementaryAbelian 2 (simpleRemainder Q split i) ∧
      Nat.card (simpleRemainder Q split i) = 16 ∧
      ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ = ⊥ ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ = rootAt Q split j (Q.simple i) ∧
      (frattini (simpleRemainder Q split j)).map (simpleRemainder Q split j).subtype =
        rootAt Q split j (Q.simple i) ∧
      Nat.card S = 64 := by
  have hderived : Nat.card (⁅(parabolic L S j).pCoreIn 2,
      (parabolic L S j).pCoreIn 2⁆ : Subgroup G) = 2 := by
    have hd := card_dvd_of_le hbound
    rw [hZ] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hc | hc
    · exact (hnonzero (card_eq_one.mp hc)).elim
    · exact hc
  exact marked_quadratic_linear_roots Q e h split hm i j hij 2 (by decide)
    hVi hVj hindexi hindexj helem hQi hQj hderived

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
