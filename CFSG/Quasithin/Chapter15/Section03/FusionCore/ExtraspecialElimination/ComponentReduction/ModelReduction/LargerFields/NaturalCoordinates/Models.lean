module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.StrictModels
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceActions
public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Theory.Representation.SL2NaturalFirstCohomology

/-!
# Selecting the SL₂ natural module from the complete source list

Characteristic-two SL₂ contains no element of order four. The checked
strict-ratio model comparisons exclude SL₃, Sp₄, A₆, SL₄(2) and SL₅(2).
The actual long-root word E(1)B(1) has square A(1), so it has order four
in G₂ and in the binary derived subgroup. Explicit permutations handle
the remaining alternating and symmetric endpoints; the triple cover is
excluded by its nontrivial center. Thus the full B.4.2 list leaves only
the natural SL₂ action, and B.5.1's three reducible cases are impossible.

The result consumes complete enumerated source conclusions. It does not
assume a selected natural action or assert either universal classification.

Source: Aschbacher–Smith, B.4.2, printed p.86, B.5.1(1), printed p.99,
and their application in 15.3.49, printed p.1144. The imported octonion
root calculations retain their ATLAS attribution and LICENSES/ATLAS.txt.
-/

public section

open Subgroup Representation Representation.BinaryOffender Matrix
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates

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

private theorem symmetric_has_order_four (n : ℕ) (hn : n = 5 ∨ n = 7 ∨ n = 8) :
    ∃ g : Equiv.Perm (Fin n), orderOf g = 4 := by
  rcases hn with rfl | rfl | rfl
  all_goals
    refine ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3,
      orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_⟩ <;> decide +kernel

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

/-- Eliminate all non-SL₂ alternatives in the full irreducible list. -/
theorem select_irreducible (ρ : Representation (ZMod 2) D V)
    (e : D ≃* SL(2,F)) {J : Subgroup D}
    (h : IrreducibleActionCase ρ ⊤ J) :
    ∃ B : BinaryField, Nonempty (ActionEquiv
      (ρ.comp (⊤ : Subgroup D).subtype) (linearNatural B 2)) := by
  let eL := (Subgroup.topEquiv (G := D)).trans e
  cases h with
  | linearTwo B _ f _ _ => exact ⟨B, ⟨f⟩⟩
  | linearThree B _ f _ => exact (not_strict eL (Or.inl ⟨B, ⟨f.groupEquiv⟩⟩)).elim
  | symplectic B hn _ f _ =>
    exact (not_strict eL (Or.inr (Or.inl ⟨B, hn, ⟨f.groupEquiv⟩⟩))).elim
  | symplecticTwo f _ =>
    exact (not_strict eL (Or.inr (Or.inr (Or.inl
      ⟨f.subgroupEquiv.trans binarySymplecticDerivedEquiv⟩)))).elim
  | g2 B _ _ f _ _ =>
    exact (no_four eL (f.groupEquiv.symm (Atlas.G2.rootE 1 * Atlas.G2.rootB 1))
      ((f.groupEquiv.symm.orderOf_eq _).trans g2_root_order_four)).elim
  | g2Two f _ _ =>
    exact (not_model eL f.subgroupEquiv.symm.toMonoidHom
      f.subgroupEquiv.symm.injective g2Derived_has_order_four).elim
  | symmetric n hn f _ _ =>
    exact (not_model e (J.subtype.comp f.action.groupEquiv.symm.toMonoidHom)
      (J.subtype_injective.comp f.action.groupEquiv.symm.injective)
      (symmetric_has_order_four n (hn.imp_right Or.inl))).elim
  | alternatingSix _ f _ _ =>
    exact (not_strict eL (Or.inr (Or.inr (Or.inl ⟨f.groupEquiv⟩)))).elim
  | alternatingSeven _ _ f _ _ _ =>
    exact (not_model eL f.symm.toMonoidHom f.symm.injective alternatingSeven_has_order_four).elim
  | tripleSix _ f _ => exact (not_triple eL f.centerEquiv).elim
  | binaryLinear n hn _ f _ =>
    rcases hn with rfl | rfl
    · exact (not_strict eL (Or.inr (Or.inr (Or.inr (Or.inl ⟨f.groupEquiv⟩))))).elim
    · exact (not_strict eL (Or.inr (Or.inr (Or.inr (Or.inr ⟨f.groupEquiv⟩))))).elim
  | orthogonalSix _ _ f _ _ =>
    exact (not_strict eL (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨f.groupEquiv.trans alternatingEightLinearEquiv⟩))))).elim
  | symmetricEight _ f _ =>
    exact (not_strict eL (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨f.subgroupEquiv.trans alternatingEightLinearEquiv⟩))))).elim
  | exteriorFive _ _ f _ _ _ =>
    exact (not_strict eL (Or.inr (Or.inr (Or.inr (Or.inr ⟨f⟩))))).elim

/-- The reducible alternatives require groups with an element of order four. -/
theorem select_movedSection (ρ : Representation (ZMod 2) D V)
    (e : D ≃* SL(2,F)) (s : MovedSection ρ ⊤)
    (h : QuasisimpleActionCase ρ ⊤ s) :
    ∃ B : BinaryField, Nonempty (ActionEquiv
      (s.action.comp (⊤ : Subgroup D).subtype) (linearNatural B 2)) := by
  let eL := (Subgroup.topEquiv (G := D)).trans e
  cases h with
  | irreducible _ _ _ hs _ => exact select_irreducible s.action e hs
  | doubleThree B _ f _ _ => exact (not_strict eL (Or.inl ⟨B, ⟨f.groupEquiv⟩⟩)).elim
  | naturalDual n hn _ hf =>
    obtain ⟨f⟩ := hf
    rcases hn with rfl | rfl
    · exact (not_strict eL (Or.inr (Or.inr (Or.inr (Or.inl ⟨f.groupEquiv⟩))))).elim
    · exact (not_strict eL (Or.inr (Or.inr (Or.inr (Or.inr ⟨f.groupEquiv⟩))))).elim
  | repeatedNatural n r hn _ _ _ hf =>
    obtain ⟨f⟩ := hf
    rcases hn with rfl | rfl
    · exact (not_strict eL (Or.inr (Or.inr (Or.inr (Or.inl ⟨f.groupEquiv⟩))))).elim
    · exact (not_strict eL (Or.inr (Or.inr (Or.inr (Or.inr ⟨f.groupEquiv⟩))))).elim
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.NaturalCoordinates
