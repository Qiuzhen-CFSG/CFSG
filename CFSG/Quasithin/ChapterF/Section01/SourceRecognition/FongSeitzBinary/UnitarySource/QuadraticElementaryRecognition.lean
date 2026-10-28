module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.QuadraticNoncommutation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.FactorProfileRecognition

/-!
# U₄ recognition from the elementary quadratic factor profile

On the same marked split quotient, the two original PSL₂ factor quotients
construct the larger root actor and the two simple-root orders. The ordered
unipotent product then gives an elementary radical of order |F|². Reflection
movement and the minimum-degree argument force a nonzero opposite-root
commutator, so the other original parabolic core is nonabelian. Its transfer
uses the exact original-core derived order through the marked endpoint;
there is no projective or central kernel discarded by this argument.

The existing quadratic recognition theorem now constructs the full U₄
comparison without a nonabelian-core premise. The model equivalence induces
both endpoint maps and the whole overlap, and the original specialization
retains literal Q.q representatives. Binary opposite factors and both
orientations are included. No field-degree parameter is needed for the
catalogue application: it is recovered from the given finite field.

Only the original factor markings with quadratic field orders, the elementary
larger-endpoint core, F.1.1, and the same marked split quotient of rotation
four remain inputs. The earlier profile and quotient producers still own
those inputs; this is not exhaustive seven-row selection. The literal
Chapter 12 application is QuadraticElementaryApplications.

Source: Fong--Seitz I (3G), (4B), (6A)(b), pp.14--16,19--22,37--38;
II (8B), pp.201--202; DGS (11.7), pp.174--175 and Theorem D, p.224.
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
  (helem : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2))

include mark h split hm hij μi μj hfields helem in
/-- The quadratic factor orders and elementary larger core force the other
original core to be nonabelian. -/
theorem quadratic_factor_opposite_core_nonabelian :
    ⁅(parabolic L S j).pCoreIn 2,(parabolic L S j).pCoreIn 2⁆ ≠ ⊥ := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hVi := MarkedLocal.linear_remainder_le_kernel Q mark h split i Ti hTi μi
  have hVj := MarkedLocal.linear_remainder_le_kernel Q mark h split j Tj hTj μj
  let := QuadrangleStructure.marked_remainder_elementary Q mark split i hVi helem
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
  have hnonzero :=
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.quadratic_elementary_cross_nonzero
      Q split hm i j hij hVi μ (show 1 < 2*(n : ℕ) by have := n.pos; omega) hF hcard
  intro hzero
  have hderived : ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ = ⊥ := by
    apply card_eq_one.mp
    rw [QuadrangleStructure.marked_remainder_derived_card Q mark h split j hVj,hzero]
    exact Subgroup.card_bot
  apply hnonzero
  have hroots := Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.opposite_roots_le_remainder
    Q split i j hij
  exact bot_unique ((commutator_mono hroots.1 hroots.2).trans hderived.le)

include mark h split hm hij μi μj hfields helem in
/-- The complete U₄ catalogue comparison with opposite-core nonabelianity
and every auxiliary actor/profile premise discharged. -/
theorem marked_elementary_quadratic_unitaryFour_catalogue :
    Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) := by
  have hne := quadratic_factor_opposite_core_nonabelian Q mark h split hm i j hij μi μj hfields helem
  let := Fintype.ofFinite k
  obtain ⟨n,_,hn⟩ := FiniteField.card k 2
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have hk : Nat.card k = 2^(n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  exact marked_quadratic_factor_unitaryFour_catalogue Q mark h split hm i j hij μi μj
    hfields helem hne n hk

open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Representation.OrthogonalFourMinus.FiniteModel
open UnitaryPresentation

include mark h split hm hij μi μj hfields helem in
/-- The model equivalence induces both endpoint maps and the entire overlap
on the same source quotient, with opposite-core nonabelianity discharged. -/
theorem marked_elementary_quadratic_unitaryFour_comparison
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
        e.symm (mark.right a : X ⧸ Q.D)) := by
  have hne := quadratic_factor_opposite_core_nonabelian Q mark h split hm i j hij μi μj hfields helem
  obtain ⟨fi,hfi,hki,_⟩ := MarkedLocal.linear_actor_quotient_of_factor Q mark h split i μi
  obtain ⟨fj,hfj,hkj,_⟩ := MarkedLocal.linear_actor_quotient_of_factor Q mark h split j μj
  have hQi := MarkedLocal.sylow_core_elementary_of_linear_actor h i fi hki
  have hQj := MarkedLocal.sylow_core_elementary_of_linear_actor h j fj hkj
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hVi := MarkedLocal.linear_remainder_le_kernel Q mark h split i Ti hTi μi
  have hVj := MarkedLocal.linear_remainder_le_kernel Q mark h split j Tj hTj μj
  have hindexi : (commonBorel L S).relIndex (parabolic L S i) = Nat.card F + 1 := by
    rw [QuadrangleStructure.marked_commonBorel_root_index Q mark h split i,
      MarkedLocal.simpleRoot_card_linear Q mark h split i Ti hTi μi,Nat.add_comm]
  have hindexj : (commonBorel L S).relIndex (parabolic L S j) = Nat.card k + 1 := by
    rw [QuadrangleStructure.marked_commonBorel_root_index Q mark h split j,
      MarkedLocal.simpleRoot_card_linear Q mark h split j Tj hTj μj,Nat.add_comm]
  exact marked_quadratic_unitaryFour_comparison Q mark h split hm i j hij hVi hVj
    fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne n hk

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
  (helem : IsElementaryAbelian 2 ((parabolic L S i).pCoreIn 2))
  (n : ℕ) [NeZero n] (hk : Nat.card k = 2^n)

include h split hm hij μi μj hfields helem hk in
/-- The complete comparison evaluates on the literal original quotient map
at both endpoints and at every element of the whole overlap. -/
theorem original_elementary_quadratic_unitaryFour_comparison :
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
        e.symm (Q.q ⟨a,parabolic_le_generated 1 a.property⟩)) := by
  obtain ⟨e,c,hl,hm',hr⟩ := marked_elementary_quadratic_unitaryFour_comparison Q (originalMarkedIso Q)
    h split hm i j hij μi μj hfields helem n hk
  refine ⟨e,c,?_,?_,?_⟩
  · intro a
    rw [hl,originalMarkedIso_left_apply]
  · intro a
    rw [hm',originalMarkedIso_middle_apply]
  · intro a
    rw [hr,originalMarkedIso_right_apply]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
