module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.SourceContracts
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Ordinary components in the complete FF alternatives

Each B.5.6 product factor is S₃ or has an ordinary component. The degree-one
SL₂ case uses the actual S₃ isomorphism; higher SL₂ and SL₃ use their genuine
quasisimplicity, while S₅ contributes A₅. The outer case contributes its A₆
factor and the hyperplane case contributes SL₃(2). In the quasisimple-Fitting
case only F* is used; no perfectness of the whole actor is inferred.

This exhausts all alternatives, including the trivial actor. It uses none of
the outer case's disputed module-splitting fields. The supplied universal
classification is still an earlier-source input, not proved here.

The matrix arguments reuse the attributed Theory ATLAS ports and adapt the
intrinsic model calculations in the existing Chapter 15
`ComponentExistence/ProductComponents/FactorModels.lean`; no later Chapter 15
conclusion is imported or used. Source: Aschbacher–Smith B.5.6, printed p.105.
-/

@[expose] public section
open Subgroup Representation Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.NonquasisimpleFactorization
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives

private theorem slTwo_quasisimple (F : BinaryField) (hn : 2 ≤ F.degree) :
    IsQuasisimple SL(2, F.Carrier) := by
  have hcard : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hn
  have hfield : ∃ a : F.Carrier, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
    obtain ⟨x, hx⟩ : IsCyclic F.Carrierˣ := inferInstance
    refine ⟨x, Units.ne_zero x, fun h ↦ ?_⟩
    grw [Nat.card_eq_card_units_add_one F.Carrier,
      ← orderOf_eq_card_of_forall_mem_zpowers hx,
      orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at hcard
    omega
  exact { toIsPerfect := ⟨Matrix.SL2.commutator_eq_top hfield.choose_spec.1 hfield.choose_spec.2⟩
          simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard }

private theorem slThree_quasisimple (F : BinaryField) : IsQuasisimple SL(3, F.Carrier) :=
  { toIsPerfect := Atlas.sl_perfect 3 (by decide)
    simple := Atlas.psl_simple_high_rank 3 (by decide) }

private theorem alternating_quasisimple (n : ℕ) (hn : 5 ≤ n) :
    IsQuasisimple (alternatingGroup (Fin n)) := by
  let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa)
  exact { toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simpa)⟩
          simple := ((QuotientGroup.quotientMulEquivOfEq
            (alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega)))).trans
              QuotientGroup.quotientBot).isSimpleGroup }

private theorem has_component_of_quasisimple {D : Type*} [Group D] [IsQuasisimple D] :
    ∃ L : Subgroup D, IsComponent D L :=
  ⟨⊤, .top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩

private theorem factor_cases {D : Type*} [Group D] (h : FactorModel D) :
    Nonempty (D ≃* Equiv.Perm (Fin 3)) ∨ ∃ L : Subgroup D, IsComponent D L := by
  cases h with
  | linearTwo F e =>
    by_cases hn : F.degree = 1
    · left
      have hc : Nat.card F.Carrier = 2 := by rw [F.card_eq, hn]; rfl
      let := Fintype.ofFinite F.Carrier
      let f : F.Carrier ≃+* ZMod 2 :=
        (ZMod.ringEquivOfPrime F.Carrier (by decide)
          (by simpa only [← Nat.card_eq_fintype_card] using hc)).symm
      obtain ⟨g⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
      exact ⟨e.trans ((Atlas.fieldEquivSL 2 f).trans g)⟩
    · have hn : 2 ≤ F.degree := by have := F.degree_pos; omega
      let := slTwo_quasisimple F hn
      let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e.symm
      exact Or.inr has_component_of_quasisimple
  | symmetricFive e =>
    let := alternating_quasisimple 5 (by decide)
    have h : IsComponent (Equiv.Perm (Fin 5)) (alternatingGroup (Fin 5)) :=
      ⟨(inferInstance : (alternatingGroup (Fin 5)).Normal).isSubnormal, inferInstance⟩
    exact Or.inr ⟨_, h.map_equiv e.symm⟩
  | linearThree F _ e =>
    let := slThree_quasisimple F
    let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e.symm
    exact Or.inr has_component_of_quasisimple

private theorem product_component {D E : Type*} [Group D] [Group E]
    {L : Subgroup D} (hL : IsComponent D L) :
    IsComponent (D × E) (L.prod (⊥ : Subgroup E)) := by
  refine ⟨?_, ?_⟩
  · have he : L.prod (⊥ : Subgroup E) =
        L.comap (MonoidHom.fst D E) ⊓ (⊥ : Subgroup E).comap (MonoidHom.snd D E) := rfl
    rw [he]
    exact (hL.1.comap _).inf ((inferInstance : (⊥ : Subgroup E).Normal).isSubnormal.comap _)
  · let := hL.2
    exact IsQuasisimple.of_mulEquiv ((prodEquiv L (⊥ : Subgroup E)).trans .prodUnique).symm

private theorem lift_component {D : Type*} [Group D] (N : Subgroup D)
    (hN : N.IsSubnormal) {L : Subgroup N} (hL : IsComponent N L) :
    IsComponent D (L.map N.subtype) := by
  let := hL.2
  exact ⟨hL.1.trans' hN,
    IsQuasisimple.of_mulEquiv (L.equivMapOfInjective N.subtype N.subtype_injective)⟩

private theorem product_cases {D E F : Type*} [Group D] [Group E] [Group F]
    (e : D ≃* E × F) (hE : FactorModel E) (hF : FactorModel F) :
    (∃ L : Subgroup D, IsComponent D L) ∨
      Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  rcases factor_cases hE with he | ⟨L, hL⟩
  · obtain ⟨eE⟩ := he
    rcases factor_cases hF with hf | ⟨L, hL⟩
    · obtain ⟨eF⟩ := hf
      exact Or.inr ⟨e.trans (MulEquiv.prodCongr eE eF)⟩
    · exact Or.inl ⟨_, (product_component (E := E) hL).map_equiv
        ((MulEquiv.prodComm : F × E ≃* E × F).trans e.symm)⟩
  · exact Or.inl ⟨_, (product_component (E := F) hL).map_equiv e.symm⟩

/-- Every complete B.5.6 alternative has an ordinary component, is trivial,
or is literally S₃ or S₃×S₃. The outer and hyperplane branches contribute
ordinary components; no perfectness of their whole actors is asserted. -/
theorem source_group_cases {D V : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
    (h : ProjectiveLine.SourceAlternative ρ) :
    Subsingleton D ∨ (∃ L : Subgroup D, IsComponent D L) ∨
      Nonempty (D ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  cases h with
  | trivial h => exact Or.inl h
  | quasisimple hq _ =>
    exact Or.inr (Or.inl ⟨generalizedFitting D,
      (inferInstance : (generalizedFitting D).Normal).isSubnormal, hq⟩)
  | symmetricThree c => exact Or.inr (Or.inr (Or.inl ⟨c.equiv⟩))
  | twoFactors c =>
    rcases product_cases c.product.equiv.symm
        (c.firstCase.factorModel ρ) (c.secondCase.factorModel ρ) with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  | outerSixThree c =>
    let := alternating_quasisimple 6 (by decide)
    let : IsQuasisimple c.first := IsQuasisimple.of_mulEquiv c.firstEquiv.symm
    obtain ⟨L, hL⟩ := has_component_of_quasisimple (D := c.first)
    have hh := (product_component (E := c.second) hL).map_equiv c.product
    exact Or.inr (Or.inl ⟨_, lift_component (c.first ⊔ c.second) c.product_normal.isSubnormal hh⟩)
  | hyperplane c =>
    let : IsQuasisimple SL(3, ZMod 2) := slThree_quasisimple BinaryField.two
    let : IsQuasisimple c.first := IsQuasisimple.of_mulEquiv c.firstEquiv.symm
    obtain ⟨L, hL⟩ := has_component_of_quasisimple (D := c.first)
    exact Or.inr (Or.inl ⟨_, (product_component (E := c.second) hL).map_equiv c.product.equiv⟩)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.NonquasisimpleFactorization
