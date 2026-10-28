module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.StrictModels
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels.Groups
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup

/-!
# The full B.4.2 sieve for an actual characteristic-two PSL₂ component

All eleven action alternatives are inspected. The five strict-ratio models
are excluded by the existing order-four obstruction. The same obstruction
excludes A₇ and both G₂ cases: the explicit product B(1)E(1) squares to A(1)
and lies in the actual binary derived group. A nontrivial center excludes
3·A₆. The surviving natural action retains the original field exponent;
the exceptional action retains the full offender-generated S₅ and its
marked A₅ subgroup, and forces n = 2.

`constituentCase_of_ff` applies the complete universal B.4.2 input only to
an action satisfying its genuine faithful irreducible hypotheses. Likewise
`not_strong_of_b4` concerns that reduced action; it does not supply the
irreducible reduction for an arbitrary KT actor or its section images.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2,
printed pp.86–87, used in 13.8.20, printed pp.954–955. Concrete G₂ root
identities are reused from the attributed ATLAS ports in the imports;
no additional ATLAS source is copied here.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups CharTwo
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo

private theorem g2_four_square {F : Type*} [Field F] [CharP F 2] :
    (Atlas.G2.rootB (1 : F) * Atlas.G2.rootE 1)^2 = Atlas.G2.rootA 1 := by
  open Atlas.G2 in
    have h : unipotentProductParameters ![0,1,0,0,1,0] ![0,1,0,0,1,0] =
        (![1,0,0,0,0,0] : Fin 6 → F) := by
      ext i
      fin_cases i <;> simp [unipotentProductParameters, CharTwo.add_self_eq_zero]
    have hg : rootB (1 : F) * rootE 1 = unipotentProduct ![0,1,0,0,1,0] := by
      simp [unipotentProduct]
    rw [hg, pow_two, unipotentProduct_mul, h]
    simp [unipotentProduct]

private theorem g2_four_order {F : Type*} [Field F] [CharP F 2] :
    orderOf (Atlas.G2.rootB (1 : F) * Atlas.G2.rootE 1) = 4 := by
  apply @orderOf_eq_prime_pow _ _ _ 1 2 ⟨Nat.prime_two⟩
  · rw [pow_one, g2_four_square]
    intro h
    exact one_ne_zero (Atlas.G2.rootA_injective (h.trans Atlas.G2.rootA_zero.symm))
  · rw [show 2 ^ (1 + 1) = 2 * 2 by decide, pow_mul, g2_four_square,
      pow_two, Atlas.G2.rootA_add, CharTwo.add_self_eq_zero, Atlas.G2.rootA_zero]

private theorem g2Derived_has_order_four :
    ∃ g : commutator (Atlas.G2.Model (ZMod 2)), orderOf g = 4 := by
  have hm : Atlas.G2.rootB (1 : ZMod 2) * Atlas.G2.rootE 1 ∈
      commutator (Atlas.G2.Model (ZMod 2)) := by
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
    exact Subgroup.mul_mem _ (Atlas.G2.BinaryException.rootB_in_H _)
      (Atlas.G2.BinaryException.rootE_in_H _)
  exact ⟨⟨_, hm⟩, (Subgroup.orderOf_coe _).symm.trans g2_four_order⟩

private theorem alternatingSeven_has_order_four :
    ∃ g : alternatingGroup (Fin 7), orderOf g = 4 := by
  let g : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5, by change Equiv.Perm.sign _ = 1; decide +kernel⟩
  exact ⟨g, @orderOf_eq_prime_pow _ _ g 1 2 ⟨Nat.prime_two⟩
    (by decide +kernel) (by decide +kernel)⟩

variable {F L : Type*} [Field F] [Finite F] [CharP F 2] [Group L]

private theorem exclude_strict (e : L ≃* PSL(2,F)) (h : StrictRatioModel L) : False := by
  obtain ⟨g, hg⟩ := h.exists_order_four
  exact psl_order_ne_four (e g) ((e.orderOf_eq g).trans hg)

omit [Finite F] in
private theorem exclude_tripleSix (e : L ≃* PSL(2,F))
    (z : center L ≃* Multiplicative (ZMod 3)) : False := by
  have h := Nat.card_congr ((centerCongr e).symm.trans z).toEquiv
  rw [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot, Subgroup.card_bot] at h
  norm_num [Nat.card_zmod] at h

universe u v
variable {D : Type u} [Group D] [Finite D] {V : Type v}
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- The two actual surviving actions, retaining group/module coordinates,
the marked offender subgroup, and the source field exponent. -/
inductive ConstituentCase (L J : Subgroup D) (n : ℕ) : Prop
  | natural (E : BinaryField) (degree : E.degree = n) (generated : J = L)
      (e : ActionEquiv (ρ.comp L.subtype) (linearNatural E 2))
  | five (degree : n = 2)
      (e : MarkedActionEquiv ρ J L (BinaryPermutation.naturalRepresentation (Fin 5))
        (alternatingGroup (Fin 5)))

/-- The complete eleven-case list leaves precisely natural or the marked S₅ action. -/
theorem constituentCase_of_full_list {L J : Subgroup D}
    (hL : Theory.GroupTheory.IsComponent D L) {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL L 2 (2^n))
    (hc : IrreducibleActionCase ρ L J) : ConstituentCase ρ L J n := by
  obtain ⟨F, _, _, hF, ⟨eL⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hm : ClassicalGroup.IsPSL L 2 (2^n) := ⟨F, inferInstance, inferInstance, hF, ⟨eL⟩⟩
  cases hc with
  | linearTwo E hj e _ _ =>
    exact .natural E (GroupComparisons.linearTwo hL le_rfl hn hm E e.groupEquiv).2 hj e
  | linearThree E _ e _ => exact (exclude_strict eL (Or.inl ⟨E, ⟨e.groupEquiv⟩⟩)).elim
  | symplectic E hE _ e _ =>
    exact (exclude_strict eL (Or.inr (Or.inl ⟨E, hE, ⟨e.groupEquiv⟩⟩))).elim
  | symplecticTwo e _ =>
    exact (exclude_strict eL (Or.inr (Or.inr (Or.inl
      ⟨e.subgroupEquiv.trans binarySymplecticDerivedEquiv⟩)))).elim
  | g2 E _ _ e _ _ =>
    exact (not_equiv_psl_of_order_four _ (g2_four_order (F := E.Carrier))
      ⟨eL.symm.trans e.groupEquiv⟩).elim
  | g2Two e _ _ =>
    obtain ⟨g, hg⟩ := g2Derived_has_order_four
    exact (not_equiv_psl_of_order_four g hg ⟨eL.symm.trans e.subgroupEquiv⟩).elim
  | symmetric d hd e _ _ =>
    rcases hd with rfl | rfl
    · exact .five (GroupComparisons.symmetricFive hL e.contained hn hm e.action.groupEquiv).2 e
    · obtain ⟨g, hg⟩ := alternatingSeven_has_order_four
      exact (not_equiv_psl_of_order_four g hg ⟨eL.symm.trans e.subgroupEquiv⟩).elim
  | alternatingSix _ e _ _ =>
    exact (exclude_strict eL (Or.inr (Or.inr (Or.inl ⟨e.groupEquiv⟩)))).elim
  | alternatingSeven _ _ e _ _ _ =>
    obtain ⟨g, hg⟩ := alternatingSeven_has_order_four
    exact (not_equiv_psl_of_order_four g hg ⟨eL.symm.trans e⟩).elim
  | tripleSix _ a _ => exact (exclude_tripleSix eL a.centerEquiv).elim
  | binaryLinear d hd _ e _ =>
    rcases hd with rfl | rfl
    · exact (exclude_strict eL (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.groupEquiv⟩))))).elim
    · exact (exclude_strict eL (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.groupEquiv⟩))))).elim
  | orthogonalSix _ _ e _ _ =>
    exact (exclude_strict eL (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨e.groupEquiv.trans alternatingEightLinearEquiv⟩))))).elim
  | symmetricEight _ e _ =>
    exact (exclude_strict eL (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨e.subgroupEquiv.trans alternatingEightLinearEquiv⟩))))).elim
  | exteriorFive _ _ e _ _ _ =>
    exact (exclude_strict eL (Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩))))).elim

open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open Theory.GroupTheory

variable [Finite V]

/-- Apply B.4.2 after verifying all hypotheses on this faithful action image. -/
theorem constituentCase_of_ff {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
    (h : B4Hypotheses 𝒦 ρ) (hff : IsFFModule ρ)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (generalizedFitting D) 2 (2^n)) :
    ConstituentCase ρ (generalizedFitting D) (offenderSubgroup ρ) n := by
  obtain ⟨A, hA⟩ := h.exists_bestOffender hff
  exact constituentCase_of_full_list ρ
    ⟨(inferInstance : (generalizedFitting D).Normal).isSubnormal, h.quasisimple⟩
    hn hm (hB42 D V ρ A hA)

/-- No reduced faithful irreducible B.4 action with this component is strong FF. -/
theorem not_strong_of_b4 {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
    (h : B4Hypotheses 𝒦 ρ) {n : ℕ}
    (hm : ClassicalGroup.IsPSL (generalizedFitting D) 2 (2^n)) :
    ¬ IsStrongFFModule ρ := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  intro hs
  let a : StrongPSLTwoAction.{u,v,0} 𝒦 F := {
    Actor := D
    Space := V
    representation := ρ
    hypotheses := h
    strong := hs
    componentEquiv := e }
  exact not_strictRatioModel_psl (a.strictRatioModel hB42)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo

end
