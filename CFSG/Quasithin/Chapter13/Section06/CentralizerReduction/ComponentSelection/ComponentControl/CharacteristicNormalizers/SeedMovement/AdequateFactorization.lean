module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.CharacteristicNormalizers.SeedMovement.NonquasisimpleFactorization.Action
public import Theory.GroupTheory.CComponent.NonquasisimpleAction
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
/-!
# Thompson factorization from the corrected B.5.6 contract

The native adequate classification retains the complete alternatives and
uses the literal outer A₆–C₃ group configuration in the disputed splitting
case. Its action identifications give exactly the same group sieve as the
original conditional factorization: an ordinary component, the trivial
actor, S₃, or S₃×S₃. Normality of the outer product follows from its actual
conjugation automorphisms and generation statement.

We apply this sieve to the full offender subgroup of H/C_H(W), with its
inverse-image SQTK cover, and reuse the proved nonquasisimple-component
exclusions and Thompson-image inclusion. This does not use the old
whole-module splitting clause or assert a universal classification.

The private intrinsic group calculations adapt the prerequisite's
NonquasisimpleFactorization.Classification implementation to the native
contracts, using the same attributed ATLAS model proofs. Source:
Aschbacher–Smith, combined 1 March 2004 manuscript, B.2.5–7, pp.76–77,
B.5.3–6, pp.104–105; see docs/quasithin-proof-basis.md for the outer clause.
-/

@[expose] public section
open Subgroup Representation Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.SeedMovement.AdequateFactorization
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives
open NonquasisimpleFactorization
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


private def field (F : ChapterB.QuasisimpleSource.BinaryField) : BinaryField where
  Carrier := F.Carrier
  degree := F.degree
  degree_pos := F.degree_pos
  card_eq := F.card_eq

private theorem native_factor {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) {A : Subgroup D} {U : Subrepresentation ρ}
    (h : ChapterB.SourceInduction.SourceFactorCase ρ A U) : FactorModel A := by
  cases h with
  | natural _ h =>
    cases h with
    | linearTwo F h => exact h.elim fun e => .linearTwo (field F) e.groupEquiv
    | symmetricFive h => exact h.elim fun e => .symmetricFive e.groupEquiv
    | linearThree F ho h => exact h.elim fun e => .linearThree (field F) ho e.groupEquiv
  | doubleNatural F ho _ h => exact h.elim fun e => .linearThree (field F) ho e.groupEquiv
  | exceptional _ h => exact .linearThree BinaryField.two (by decide) h.natural.groupEquiv

private theorem outer_normal {D : Type*} [Group D] (c : ChapterB.OuterSixThreeShape D) :
    (c.first ⊔ c.second).Normal := by
  have hn : c.element ∈ normalizer ((c.first ⊔ c.second : Subgroup D) : Set D) := by
    obtain ⟨a, ha, _⟩ := c.firstOuter
    obtain ⟨b, hb, _⟩ := c.secondOuter
    have hA : c.element ∈ normalizer (c.first : Set D) := by
      apply mem_normalizer_iff.mpr
      intro x
      constructor
      · intro hx
        exact ha ⟨x, hx⟩ ▸ (a ⟨x, hx⟩).property
      · intro hx
        let y : c.first := ⟨c.element * x * c.element⁻¹, hx⟩
        have he := ha (a.symm y)
        have hx' : (a.symm y : D) = x := by
          have he' : c.element * x * c.element⁻¹ =
              c.element * (a.symm y : D) * c.element⁻¹ := by
            simpa only [MulEquiv.apply_symm_apply] using he
          exact (mul_left_cancel (mul_right_cancel he')).symm
        exact hx' ▸ (a.symm y).property
    have hB : c.element ∈ normalizer (c.second : Set D) := by
      apply mem_normalizer_iff.mpr
      intro x
      constructor
      · intro hx
        exact hb ⟨x, hx⟩ ▸ (b ⟨x, hx⟩).property
      · intro hx
        let y : c.second := ⟨c.element * x * c.element⁻¹, hx⟩
        have he := hb (b.symm y)
        have hx' : (b.symm y : D) = x := by
          have he' : c.element * x * c.element⁻¹ =
              c.element * (b.symm y : D) * c.element⁻¹ := by
            simpa only [MulEquiv.apply_symm_apply] using he
          exact (mul_left_cancel (mul_right_cancel he')).symm
        exact hx' ▸ (b.symm y).property
    exact normalizer_inf_normalizer_le_normalizer_sup c.first c.second ⟨hA, hB⟩
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← c.generates]
  exact sup_le (c.first ⊔ c.second).le_normalizer (zpowers_le.mpr hn)

private theorem group_cases {D V : Type*} [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
    (h : ChapterB.SourceInduction.AdequateAlternative ρ) :
    Subsingleton D ∨ (∃ L : Subgroup D, IsComponent D L) ∨
      Nonempty (D ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  rcases h with ht | h
  · exact Or.inl ht
  cases h with
  | quasisimple hq _ =>
    exact Or.inr (Or.inl ⟨generalizedFitting D,
      (inferInstance : (generalizedFitting D).Normal).isSubnormal, hq⟩)
  | symmetricThree c => exact Or.inr (Or.inr (Or.inl ⟨c.equiv⟩))
  | twoFactors c =>
    rcases product_cases c.product.equiv.symm
        (native_factor ρ c.firstCase) (native_factor ρ c.secondCase) with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  | outerSixThree c =>
    let := alternating_quasisimple 6 (by decide)
    let : IsQuasisimple c.first := IsQuasisimple.of_mulEquiv c.firstEquiv.symm
    obtain ⟨L, hL⟩ := has_component_of_quasisimple (D := c.first)
    have hh := (product_component (E := c.second) hL).map_equiv c.product
    exact Or.inr (Or.inl ⟨_, lift_component (c.first ⊔ c.second) (outer_normal c).isSubnormal hh⟩)
  | hyperplane c =>
    let : IsQuasisimple SL(3, ZMod 2) := slThree_quasisimple BinaryField.two
    let : IsQuasisimple c.first := IsQuasisimple.of_mulEquiv c.firstEquiv.symm
    obtain ⟨L, hL⟩ := has_component_of_quasisimple (D := c.first)
    exact Or.inr (Or.inl ⟨_, (product_component (E := c.second) hL).map_equiv c.product.equiv⟩)

open Representation.BinaryOffender Stellmacher Theory.GroupTheory.NonquasisimpleAction
universe u v
private theorem offender_eq_bot {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal] [Group.IsPerfect K]
    (hK : K = ⊥ ∨ K.IsCComponent) (hq : IsPGroup 2 (D ⧸ K))
    (hcore : pCore 2 D = ⊥) (hnq : ¬ IsQuasisimple K)
    (hclass : ChapterB.SourceInduction.AdequateAlternative (ρ.comp (offenderSubgroup ρ).subtype)) :
    offenderSubgroup ρ = ⊥ := by
  let J := offenderSubgroup ρ
  let : J.Normal := offenderSubgroup_normal ρ
  rcases group_cases (ρ.comp J.subtype) hclass with ht | ⟨L, hL⟩ | hs | hp
  · let := ht
    exact J.eq_bot_iff_forall.mpr (fun x hx => congrArg Subtype.val
      (Subsingleton.elim (⟨x, hx⟩ : J) 1))
  · have hc : IsComponent D (L.map J.subtype) := by
      let := hL.2
      exact ⟨hL.1.trans' (inferInstance : J.Normal).isSubnormal,
        IsQuasisimple.of_mulEquiv (L.equivMapOfInjective J.subtype J.subtype_injective)⟩
    exact (no_ordinary_components K hK hq hnq _ hc).elim
  · exact hs.elim (normal_symmetricThree_eq_bot K J hq hcore)
  · exact hp.elim (normal_symmetricThreePair_eq_bot K J hq hcore)

variable {H : Type u} [Group H] [Finite H]
/-- The intrinsic factorization, with only the corrected universal B.5.6 input. -/
theorem thompson_factorization {𝒦 : GroupClass.{u}}
    (classification : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} 𝒦)
    (hH : IsSQTK 𝒦 H) (P : Sylow 2 H) (K W : Subgroup H)
    [K.Normal] [W.Normal] [IsElementaryAbelian 2 W]
    (hK : K.IsCComponent) (hKP : K ⊔ (P : Subgroup H) = ⊤)
    (hcore : pCore 2 (ActionQuotient W) = ⊥)
    (hnq : ¬ IsQuasisimple (K.map (actionMk W))) :
    elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H) ∧
      normalizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H) ⊔
        centralizer (W : Set H) = ⊤ := by
  let q := actionMk W
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let B := K.map q
  let : B.Normal := (inferInstance : K.Normal).map q hq
  let := hK.perfect
  let : Group.IsPerfect B := Group.IsPerfect.map q
  have hjoin : B ⊔ (P : Subgroup H).map q = ⊤ := by
    rw [← Subgroup.map_sup, hKP, map_top_of_surjective _ hq]
  have hquot : IsPGroup 2 (ActionQuotient W ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B _ (P.isPGroup'.map q) hjoin
  have hh := offender_hypothesis (action W) q hq hH (action_faithful W) hcore
  obtain ⟨cover⟩ := hh.quotient
  let := cover.coverGroup
  let := cover.coverFinite
  let := cover.kernelNormal
  have hnative : ChapterB.SourceInduction.FFHypothesis 𝒦
      ((action W).comp (offenderSubgroup (action W)).subtype) :=
    ⟨hh.finite_module, hh.faithful, hh.twoCore, hh.generated,
      ⟨{ Cover := cover.Cover
         kernel := cover.kernel
         sqtk := cover.sqtk
         equiv := cover.equiv }⟩⟩
  have hz := offender_eq_bot (action W) B (ccomponent_image_or_bot hK q hq)
    hquot hcore hnq (classification _ _ _ hnative)
  have hj : (elementaryAbelianMaxJ (P : Subgroup H)).map q = ⊥ :=
    eq_bot_iff.mpr (hz ▸ thompson_image_le P W)
  have hc : elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H) := by
    simpa only [q, actionMk, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hj
  exact ⟨hc, thompson_frattini P W hc⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.SeedMovement.AdequateFactorization

end
