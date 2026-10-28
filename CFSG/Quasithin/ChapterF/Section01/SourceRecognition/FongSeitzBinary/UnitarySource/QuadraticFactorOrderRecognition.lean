module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.QuadraticFrattini
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.QuadraticElementaryRecognition

/-!
# U₄ recognition from the quadratic orders of the original factors

The original PSL₂ factor markings determine simple-root orders |F| and |k|.
When |F| = |k|² and the rotation has order four, the ordered unipotent
product gives the larger-endpoint radical order |F|². The actual reflection
moves the opposite root. The Frattini and minimum-degree argument therefore
makes this radical elementary, without a hypothesis on either original
core. Pulling back along the same injective endpoint map identifies the
full original larger two-core and proves its elementarity.

QuadraticElementaryRecognition then forces the opposite core to be
nonabelian and constructs the U₄ comparison. Its full Borel, both endpoint
squares and original quotient representatives are retained. The larger
actor starts at SL₂(4), so the smaller binary factor and both orientations
are included. No original endpoint perfectness is required.

Only F.1.1, the same marked split quotient of rotation four, and the actual
PSL₂ factor markings with quadratic field orders remain hypotheses. The
earlier quotient and factor-profile producers retain these inputs; this
is the selected U₄ branch, not exhaustive seven-row recognition. The literal
Chapter 12 consumer is QuadraticFactorOrderApplications.

Source: Fong--Seitz I (4B), (6A)(b), pp.19--22,37--38, and II (8B),
pp.201--202; DGS, Groups and Graphs (1985), (11.7), pp.174--175,
and Theorem D, p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
variable {G X F k : Type*} [Group G] [Group X]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
  (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,k))
  (hfields : Nat.card F = Nat.card k ^ 2)

include mark h split hm hij μi μj hfields in
/-- The original larger two-core is elementary, as forced by the quadratic
factor orders and the reflection action on its literal quotient image. -/
theorem quadratic_factor_larger_core_elementary :
    IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2) := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hVi := MarkedLocal.linear_remainder_le_kernel Q mark h split i Ti hTi μi
  have hri := MarkedLocal.simpleRoot_card_linear Q mark h split i Ti hTi μi
  have hrj := MarkedLocal.simpleRoot_card_linear Q mark h split j Tj hTj μj
  obtain ⟨fi,hfi,hki,_⟩ := MarkedLocal.linear_actor_quotient_of_factor Q mark h split i μi
  let : ((S ⊔ L i).subgroupOf (parabolic L S i)).Normal :=
    QuadrangleStructure.marked_sylow_factor_normal Q mark h split i
  obtain ⟨μ,_,_,_⟩ := QuadrangleStructure.marked_linear_localGroup Q mark h split i
    (Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.actorReflection Q split i)
    hVi _ (subgroupOf_mono _ le_sup_left) fi hfi hki
  have hprod : Nat.card (simpleRoot Q split 0) * Nat.card (simpleRoot Q split 1) =
      Nat.card F * Nat.card k := by
    have hi : i = 0 ∨ i = 1 := by omega
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (hij rfl).elim
    · rw [hri,hrj]
    · rw [hrj,hri,Nat.mul_comm]
    · exact (hij rfl).elim
  have hcard : Nat.card (simpleRemainder Q split i) = Nat.card F ^ 2 := by
    have hc := unipotent_card_simple Q split i
    rw [unipotent_card_even Q split 2 hm,hprod,hri] at hc
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := F))
    calc
      Nat.card F * Nat.card (simpleRemainder Q split i) =
          (Nat.card F * Nat.card k)^2 := hc.symm
      _ = Nat.card F * Nat.card F ^ 2 := by rw [hfields]; ring
  let := Fintype.ofFinite k
  obtain ⟨n,_,hn⟩ := FiniteField.card k 2
  have hk : Nat.card k = 2^(n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  have hF : Nat.card F = 2^(2*(n : ℕ)) := by rw [hfields,hk,←pow_mul,Nat.mul_comm]
  let :=
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.quadratic_remainder_elementary
      Q split hm i j hij hVi μ (show 1 < 2*(n : ℕ) by have := n.pos; omega) hF hcard
  have hinj : Function.Injective (MarkedLocal.endpointMap Q mark i) :=
    (Q.tits.standardParabolic {Q.simple i}).subtype_injective.comp
      (MarkedLocal.endpoint Q mark i).injective
  have he := IsElementaryAbelian.comap_of_injective (p := 2)
    (MarkedLocal.endpointMap Q mark i) hinj (simpleRemainder Q split i)
  rw [MarkedLocal.remainder_comap_of_containment Q mark split i hVi] at he
  let := he
  exact IsElementaryAbelian.map (parabolic L S i).subtype

include mark h split hm hij μi μj hfields in
/-- The selected U₄ row from factor orders, with both original core-structure
premises and every local actor premise discharged. -/
theorem marked_quadratic_factor_order_unitaryFour_catalogue :
    Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) :=
  marked_elementary_quadratic_unitaryFour_catalogue Q mark h split hm i j hij μi μj hfields
    (quadratic_factor_larger_core_elementary Q mark h split hm i j hij μi μj hfields)

open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Representation.OrthogonalFourMinus.FiniteModel
open UnitaryPresentation

include mark h split hm hij μi μj hfields in
/-- The model equivalence induces both endpoint maps and the entire overlap
on the same source quotient, with both core-structure premises discharged. -/
theorem marked_quadratic_factor_order_unitaryFour_comparison
    (n : ℕ) [NeZero n] (hk : Nat.card k = 2^n) :
    ∃ (e : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n)) ≃* (X ⧸ Q.D))
      (c : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (MarkedAmalgam.flag
          ((pointParabolicSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))).map
            (project (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))))
          ((planeParabolicSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))).map
            (project (Field n) (form (Field n) (conjugation n) (conjugation_involutive n)))) j)),
      (∀ a : parabolic L S 0, (c.left a : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))) =
        e.symm (mark.left a : X ⧸ Q.D)) ∧
      (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
        (c.middle a : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))) =
          e.symm (mark.middle a : X ⧸ Q.D)) ∧
      (∀ a : parabolic L S 1, (c.right a : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))) =
        e.symm (mark.right a : X ⧸ Q.D)) :=
  marked_elementary_quadratic_unitaryFour_comparison Q mark h split hm i j hij μi μj hfields
    (quadratic_factor_larger_core_elementary Q mark h split hm i j hij μi μj hfields) n hk

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Representation.OrthogonalFourMinus.FiniteModel
open UnitaryPresentation
variable {G F k : Type*} [Group G]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
  (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
  (μj : ((L j) ⧸ pCore 2 (L j)) ≃* PSL(2,k))
  (hfields : Nat.card F = Nat.card k ^ 2)
  (n : ℕ) [NeZero n] (hk : Nat.card k = 2^n)

include h split hm hij μi μj hfields hk in
/-- The complete comparison evaluates on the literal original quotient map
at both endpoints and at every element of the whole overlap. -/
theorem original_quadratic_factor_order_unitaryFour_comparison :
    ∃ (e : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n)) ≃* ((generated L S) ⧸ Q.D))
      (c : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (MarkedAmalgam.flag
          ((pointParabolicSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))).map
            (project (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))))
          ((planeParabolicSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))).map
            (project (Field n) (form (Field n) (conjugation n) (conjugation_involutive n)))) j)),
      (∀ a : parabolic L S 0, (c.left a : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))) =
        e.symm (Q.q ⟨a,parabolic_le_generated 0 a.property⟩)) ∧
      (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
        (c.middle a : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))) =
          e.symm (Q.q ⟨a,parabolic_le_generated 0 a.property.1⟩)) ∧
      (∀ a : parabolic L S 1, (c.right a : PSU (Field n) (form (Field n) (conjugation n) (conjugation_involutive n))) =
        e.symm (Q.q ⟨a,parabolic_le_generated 1 a.property⟩)) :=
  original_elementary_quadratic_unitaryFour_comparison Q h split hm i j hij μi μj hfields
    (quadratic_factor_larger_core_elementary Q (originalMarkedIso Q) h split hm i j hij μi μj hfields) n hk

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
