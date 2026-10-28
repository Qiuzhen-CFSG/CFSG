module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates.Transport
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates.Models
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SourceContracts
public import Theory.Representation.BinaryOffender.SectionOffender
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# Comparing the component in the full corrected B.5.1 list

A component isomorphic to characteristic-two SL₂ has no element of order four.
This excludes all the higher-rank and exceptional components in B.4.2, but
leaves two actions: the SL₂ natural action and the five-point symmetric action
above its alternating component. The latter is deliberately retained with its
actual marking and offender clause. No equality between the whole actor and
its component is asserted.

The order-four witnesses below adapt the calculations in
`LargerFields.NaturalCoordinates.Models`; the source contract used here has
the corrected projective-line clause. The G₂ calculations use the attributed
ATLAS port and LICENSES/ATLAS.txt.

Source: Aschbacher–Smith, B.4.2 p.86, B.5.1 pp.99–103, and the larger-field
step of 15.3.49 on printed p.1144 (1 March 2004 manuscript).
-/

public section

open Subgroup Representation Representation.BinaryOffender Matrix
open Representation.SL2CubicFixedSection
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.NaturalSelection

private theorem g2_root_order_four {F : Type*} [Field F] [CharP F 2] :
    orderOf (Atlas.G2.rootE (1 : F) * Atlas.G2.rootB 1) = 4 := by
  open Atlas.G2 in
  have hsq : (rootE (1 : F) * rootB 1) ^ 2 = rootA 1 := by
    have hEinv : (rootE (1 : F))⁻¹ = rootE 1 := by
      apply inv_eq_of_mul_eq_one_left
      rw [rootE_add, CharTwo.add_self_eq_zero, rootE_zero]
    have hc := Atlas.G2.ShortRootProducts.rootE_conjugate_rootB (1 : F) 1
    simp only [MulAut.conj_apply, hEinv, one_mul] at hc
    calc
      (rootE (1 : F) * rootB 1) ^ 2 = (rootE (1 : F) * rootB 1 * rootE 1) * rootB 1 := by simp only [pow_two, mul_assoc]
      _ = rootA (1 : F) * (rootB 1 * rootB 1) := by rw [hc, mul_assoc]
      _ = rootA (1 : F) := by rw [rootB_add, CharTwo.add_self_eq_zero, rootB_zero, mul_one]
  open Atlas.G2 in
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · simpa only [pow_one, hsq, ← rootA_zero (K := F)] using
      (rootA_injective.ne (one_ne_zero : (1 : F) ≠ 0))
  · change (rootE (1 : F) * rootB 1) ^ 4 = 1
    rw [show 4 = 2 * 2 from rfl, pow_mul, hsq, pow_two, rootA_add,
      CharTwo.add_self_eq_zero, rootA_zero]

private theorem g2Derived_has_order_four :
    ∃ g : commutator (Atlas.G2.Model (ZMod 2)), orderOf g = 4 := by
  open Atlas.G2 in
  let g : commutator (Model (ZMod 2)) := ⟨rootE 1 * rootB 1, by
    rw [BinaryParabolicPair.commutator_eq_longRootClosure]
    exact BinaryException.H.mul_mem (BinaryException.rootE_in_H _) (BinaryException.rootB_in_H _)⟩
  exact ⟨g, (Subgroup.orderOf_coe g).symm.trans g2_root_order_four⟩

private theorem alternatingSeven_has_order_four :
    ∃ g : alternatingGroup (Fin 7), orderOf g = 4 := by
  let g : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5, by simp [Equiv.Perm.mem_alternatingGroup]⟩
  refine ⟨g, orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_⟩
  · decide +kernel
  · decide +kernel

variable {D V F : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [Field F] [Finite F] [CharP F 2]

private theorem no_four (e : D ≃* SL(2,F)) (g : D) (hg : orderOf g = 4) : False :=
  sl_order_ne_four (e g) ((e.orderOf_eq g).trans hg)

private theorem not_strict (e : D ≃* SL(2,F)) (h : StrictRatioModel D) : False := by
  obtain ⟨g, hg⟩ := h.exists_order_four
  exact no_four e g hg

omit [Finite F] in
private theorem not_triple (e : D ≃* SL(2,F))
    (c : center D ≃* Multiplicative (ZMod 3)) : False := by
  have hcard := Nat.card_congr ((Subgroup.centerCongr e).symm.trans c).toEquiv
  rw [Representation.SL2NaturalH1.center_eq_bot, Subgroup.card_bot] at hcard
  norm_num at hcard

private theorem not_model {E : Type*} [Group E]
    (e : D ≃* SL(2,F)) (f : E →* D) (hf : Function.Injective f)
    (hE : ∃ g : E, orderOf g = 4) : False := by
  obtain ⟨g, hg⟩ := hE
  exact no_four e (f g) ((orderOf_injective f hf g).trans hg)

/-- The surviving nonnatural row retains the literal offender-generated actor,
its alternating component, and the full offender description. -/
@[expose] def FiveCase (ρ : Representation (ZMod 2) D V) (L : Subgroup D) : Prop :=
  ∃ e : MarkedActionEquiv ρ (offenderSubgroup ρ) L
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)),
    (∀ A, IsBestOffender ρ A → ChapterB.Offenders.CaseAFamily 5
      ((A.subgroupOf (offenderSubgroup ρ)).map e.action.groupEquiv.toMonoidHom)) ∧
    quadraticRatio ρ = 1

/-- Component comparison leaves the genuine five-point exception. -/
theorem natural_or_five (ρ : Representation (ZMod 2) D V) {L : Subgroup D}
    (e : L ≃* SL(2,F))
    (h : ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ)) :
    (∃ B : BinaryField, Nonempty (ActionEquiv (ρ.comp L.subtype) (linearNatural B 2))) ∨
      FiveCase ρ L := by
  cases h with
  | linearTwo B _ f _ _ => exact Or.inl ⟨B, ⟨f⟩⟩
  | linearThree B _ f _ => exact (not_strict e (Or.inl ⟨B, ⟨f.groupEquiv⟩⟩)).elim
  | symplectic B hn _ f _ =>
    exact (not_strict e (Or.inr (Or.inl ⟨B, hn, ⟨f.groupEquiv⟩⟩))).elim
  | symplecticTwo f _ =>
    exact (not_strict e (Or.inr (Or.inr (Or.inl
      ⟨f.subgroupEquiv.trans binarySymplecticDerivedEquiv⟩)))).elim
  | g2 B _ _ f _ _ =>
    exact (no_four e (f.groupEquiv.symm (Atlas.G2.rootE 1 * Atlas.G2.rootB 1))
      ((f.groupEquiv.symm.orderOf_eq _).trans g2_root_order_four)).elim
  | g2Two f _ _ =>
    exact (not_model e f.subgroupEquiv.symm.toMonoidHom
      f.subgroupEquiv.symm.injective g2Derived_has_order_four).elim
  | symmetric n hn f ho hq =>
    rcases hn with rfl | rfl
    · exact Or.inr ⟨f, ho, hq⟩
    · exact (not_model e f.subgroupEquiv.symm.toMonoidHom
        f.subgroupEquiv.symm.injective alternatingSeven_has_order_four).elim
  | alternatingSix _ f _ _ =>
    exact (not_strict e (Or.inr (Or.inr (Or.inl ⟨f.groupEquiv⟩)))).elim
  | alternatingSeven _ _ f _ _ _ =>
    exact (not_model e f.symm.toMonoidHom f.symm.injective alternatingSeven_has_order_four).elim
  | tripleSix _ f _ => exact (not_triple e f.centerEquiv).elim
  | binaryLinear n hn _ f _ =>
    rcases hn with rfl | rfl
    · exact (not_strict e (Or.inr (Or.inr (Or.inr (Or.inl ⟨f.groupEquiv⟩))))).elim
    · exact (not_strict e (Or.inr (Or.inr (Or.inr (Or.inr ⟨f.groupEquiv⟩))))).elim
  | orthogonalSix _ _ f _ _ =>
    exact (not_strict e (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨f.groupEquiv.trans alternatingEightLinearEquiv⟩))))).elim
  | symmetricEight _ f _ =>
    exact (not_strict e (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨f.subgroupEquiv.trans alternatingEightLinearEquiv⟩))))).elim
  | exteriorFive _ _ f _ _ _ =>
    exact (not_strict e (Or.inr (Or.inr (Or.inr (Or.inr ⟨f⟩))))).elim

/-- The reducible B.5.1 rows are impossible for an SL₂ component. The
remaining exception is a faithful action on the literal central quotient. -/
theorem moved_natural_or_five (ρ : Representation (ZMod 2) D V) {L : Subgroup D}
    (e : L ≃* SL(2,F)) (s : MovedSection ρ L)
    (h : ProjectiveLine.QuasisimpleActionCase ρ L s) :
    (∃ B : BinaryField, Nonempty (ActionEquiv
      (s.action.comp L.subtype) (linearNatural B 2))) ∨
      (Function.Injective s.action ∧ FiveCase s.action L) := by
  cases h with
  | irreducible _ hf _ hs _ =>
    exact (natural_or_five s.action e hs).imp_right (fun h => ⟨hf, h⟩)
  | doubleThree B _ f _ _ => exact (not_strict e (Or.inl ⟨B, ⟨f.groupEquiv⟩⟩)).elim
  | naturalDual n hn _ hf =>
    obtain ⟨f⟩ := hf
    rcases hn with rfl | rfl
    · exact (not_strict e (Or.inr (Or.inr (Or.inr (Or.inl ⟨f.groupEquiv⟩))))).elim
    · exact (not_strict e (Or.inr (Or.inr (Or.inr (Or.inr ⟨f.groupEquiv⟩))))).elim
  | repeatedNatural n r hn _ _ _ hf =>
    obtain ⟨f⟩ := hf
    rcases hn with rfl | rfl
    · exact (not_strict e (Or.inr (Or.inr (Or.inr (Or.inl ⟨f.groupEquiv⟩))))).elim
    · exact (not_strict e (Or.inr (Or.inr (Or.inr (Or.inr ⟨f.groupEquiv⟩))))).elim

/-- Quadratic action descends through the actual moved subspace and its
central quotient, without replacing the offender by an abstract isomorph. -/
theorem quadratic_on_movedSection (ρ : Representation (ZMod 2) D V)
    {L A : Subgroup D} (s : MovedSection ρ L) (hA : IsQuadratic ρ A) :
    IsQuadratic s.action A := by
  exact quadratic_of_equivariant_surjection s.space.toRepresentation s.action
    s.central.toSubmodule.mkQ s.central.toSubmodule.mkQ_surjective
    (fun _ _ => rfl) A (quadratic_subrepresentation ρ s.space hA)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.NaturalSelection
