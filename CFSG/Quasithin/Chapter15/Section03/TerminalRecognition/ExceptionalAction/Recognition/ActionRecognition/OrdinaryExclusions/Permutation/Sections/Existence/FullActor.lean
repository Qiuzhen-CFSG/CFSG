module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Permutation.Sections
import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.MarkedElimination.AlternatingSevenDimension.Orders
import Theory.GroupTheory.PResidual.NormalSubgroup
import Theory.SpecificGroups.FFG2DerivedCenter

/-!
# Natural sections when the offender actor is the full symmetric group

The two-factor and outer-six-three alternatives cannot have symmetric actor
of degree six or seven. In B.5.1, the perfect normal F* maps to the alternating
group, so the proper-extension clause gives the natural symmetric action.
We retain the source moved space and its entire central kernel, transporting
both stability witnesses along the equality of the offender and full actors.
Two-perfectness places the marked residual Y_F in that same component.

This proves the full-offender branch only. The alternating offender images
still require their own arguments; no equality of the two actors is inferred.

Source: Aschbacher–Smith, B.5.1 and B.5.6, printed pp.99 and 105, and
15.3.1's final proof, printed p.1155 (combined manuscript, 1 March 2004).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation

private def fullSpace {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {N : Subgroup D} (hN : N = ⊤)
    {L : Subgroup N} (s : MovedSection (ρ.comp N.subtype) L) : Subrepresentation ρ where
  toSubmodule := s.space.toSubmodule
  apply_mem_toSubmodule g _v hv :=
    s.space.apply_mem_toSubmodule ⟨g, hN ▸ mem_top g⟩ hv

private def fullSection {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) {N : Subgroup D} (hN : N = ⊤)
    {L : Subgroup N} (s : MovedSection (ρ.comp N.subtype) L) :
    MovedSection ρ (L.map N.subtype) where
  space := fullSpace ρ hN s
  space_eq := by
    change s.space.toSubmodule = _
    rw [s.space_eq]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨g, hg, v, hv, rfl⟩
      exact Submodule.subset_span ⟨g, mem_map_of_mem N.subtype hg, v, hv, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨_, ⟨g, hg, rfl⟩, v, hv, rfl⟩
      exact Submodule.subset_span ⟨g, hg, v, hv, rfl⟩
  central :=
    { toSubmodule := s.central.toSubmodule
      apply_mem_toSubmodule g _v hv :=
        s.central.apply_mem_toSubmodule ⟨g, hN ▸ mem_top g⟩ hv }
  central_eq := by
    rw [← fixedSpace_comp_map]
    exact s.central_eq

private def fullSectionEquiv {D W E U : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    [Group E] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D W) {N : Subgroup D} (hN : N = ⊤)
    {L : Subgroup N} (s : MovedSection (ρ.comp N.subtype) L)
    {σ : Representation (ZMod 2) E U} (e : ActionEquiv s.action σ) :
    ActionEquiv (fullSection ρ hN s).action σ where
  groupEquiv := ((MulEquiv.subgroupCongr hN).trans topEquiv).symm.trans e.groupEquiv
  linearEquiv := e.linearEquiv
  intertwines g v := e.intertwines ⟨g, hN ▸ mem_top g⟩ v

private theorem not_symmetric_product {A B : Type*} [Group A] [Group B]
    [Nontrivial A] [Nontrivial B] {n : ℕ} (hn : 5 ≤ n)
    (e : (A × B) ≃* Equiv.Perm (Fin n)) : False := by
  let P := (MonoidHom.fst A B).ker.map e.toMonoidHom
  let Q := (MonoidHom.snd A B).ker.map e.toMonoidHom
  let : P.Normal := Subgroup.Normal.map inferInstance _ e.surjective
  let : Q.Normal := Subgroup.Normal.map inferInstance _ e.surjective
  have hp : P ≠ ⊥ := by
    intro h
    obtain ⟨b, hb⟩ := exists_ne (1 : B)
    have hm : e (1, b) ∈ P := mem_map_of_mem _ rfl
    rw [h] at hm
    exact hb (congrArg Prod.snd (e.map_eq_one_iff.mp hm))
  have hq : Q ≠ ⊥ := by
    intro h
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    have hm : e (a, 1) ∈ Q := mem_map_of_mem _ rfl
    rw [h] at hm
    exact ha (congrArg Prod.fst (e.map_eq_one_iff.mp hm))
  have hP := Equiv.Perm.alternatingGroup_le_of_normal (N := P)
    (by simpa using hn) ((nontrivial_iff_ne_bot _).mpr hp)
  have hQ := Equiv.Perm.alternatingGroup_le_of_normal (N := Q)
    (by simpa using hn) ((nontrivial_iff_ne_bot _).mpr hq)
  have hbot : alternatingGroup (Fin n) = ⊥ := by
    apply le_bot_iff.mp
    intro g hg
    obtain ⟨a, ha, rfl⟩ := hP hg
    obtain ⟨b, hb, he⟩ := hQ hg
    have heq := e.injective he
    subst b
    exact e.map_eq_one_iff.mpr (Prod.ext ha hb)
  have hi : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  exact ((nontrivial_iff_ne_bot _).mp inferInstance) hbot

private theorem fitting_symmetric_image {D : Type*} [Group D] [Finite D]
    (hq : IsQuasisimple (generalizedFitting D)) {n : ℕ} (hn : 5 ≤ n)
    (e : D ≃* Equiv.Perm (Fin n)) :
    (generalizedFitting D).map e.toMonoidHom = alternatingGroup (Fin n) := by
  let _ := hq
  let _ := hq.simple
  let : Nontrivial (generalizedFitting D) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting D))).nontrivial
  let N := (generalizedFitting D).map e.toMonoidHom
  let : N.Normal := Subgroup.Normal.map inferInstance _ e.surjective
  let : Group.IsPerfect N := Group.IsPerfect.map _
  let : Nontrivial N := (e.subgroupMap (generalizedFitting D)).injective.nontrivial
  apply le_antisymm
  · rw [← alternatingGroup.commutator_perm_eq (by simpa using hn)]
    change N ≤ ⁅(⊤ : Subgroup (Equiv.Perm (Fin n))), ⊤⁆
    rw [← N.commutator_eq_self]
    exact commutator_mono le_top le_top
  · exact Equiv.Perm.alternatingGroup_le_of_normal (by simpa using hn) inferInstance

private theorem outer_natural_of_symmetric {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    {n : ℕ} (hn : n = 6 ∨ n = 7) (e : D ≃* Equiv.Perm (Fin n))
    (hq : IsQuasisimple (generalizedFitting D))
    (c : QuasisimpleSourceConclusion ρ (generalizedFitting D)) :
    IsSymmetricNatural c.sectionData.action n := by
  have hn5 : 5 ≤ n := by omega
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hproper : generalizedFitting D ≠ ⊤ := by
    intro ht
    have he := fitting_symmetric_image hq hn5 e
    rw [ht, Subgroup.map_top_of_surjective _ e.surjective] at he
    have hi := alternatingGroup.index_eq_two (α := Fin n)
    rw [← he, index_top] at hi
    omega
  have ho : OuterNaturalAction c.sectionData.action := by
    cases c.clause_one with
    | irreducible _ _ _ _ he => exact (he.resolve_left hproper).2
    | doubleThree _ ht _ _ _ => exact (hproper ht).elim
    | naturalDual _ _ ht _ => exact (hproper ht).elim
    | repeatedNatural _ _ _ _ _ ht _ => exact (hproper ht).elim
  rcases ho with ⟨m, hm5, hm8, ⟨a⟩⟩ | ⟨⟨a⟩⟩
  · have hc := Nat.card_congr (e.symm.trans a.groupEquiv).toEquiv
    rw [Nat.card_perm, Nat.card_perm, Nat.card_fin, Nat.card_fin] at hc
    have hm : m = n := by
      rcases hn with rfl | rfl <;> interval_cases m <;> norm_num [Nat.factorial] at hc <;> omega
    subst m
    exact ⟨a⟩
  · have hc := Nat.card_congr (e.symm.trans a.groupEquiv).toEquiv
    rw [Nat.card_perm, Nat.card_fin, Atlas.G2.card_Model, Nat.card_zmod] at hc
    rcases hn with rfl | rfl <;> norm_num at hc

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

private theorem quasisimple_of_full_offender {n : ℕ} (hn : n = 6 ∨ n = 7)
    (e : coreQuotient H ≃* Equiv.Perm (Fin n))
    (hN : d.offenderGroup = ⊤) (h : SourceAlternative d.offenderAction) :
    IsQuasisimple (generalizedFitting d.offenderGroup) ∧
      Nonempty (QuasisimpleSourceConclusion d.offenderAction
        (generalizedFitting d.offenderGroup)) := by
  let eN := ((MulEquiv.subgroupCongr hN).trans topEquiv).trans e
  rcases remaining_source_cases d h with h | h
  · exact h
  · rcases h with ⟨⟨c⟩⟩ | ⟨⟨c⟩⟩
    · let := MarkedElimination.AlternatingSevenDimension.factor_nontrivial
        (c.firstCase.factorModel d.offenderAction)
      let := MarkedElimination.AlternatingSevenDimension.factor_nontrivial
        (c.secondCase.factorModel d.offenderAction)
      exact (not_symmetric_product (by omega) (c.product.equiv.trans eN)).elim
    · have hc : Nat.card (c.first ⊔ c.second : Subgroup d.offenderGroup) = 1080 := by
        rw [← Nat.card_congr c.product.toEquiv, Nat.card_prod,
          Nat.card_congr c.firstEquiv.toEquiv, Nat.card_congr c.secondEquiv.toEquiv,
          nat_card_alternatingGroup]
        norm_num [Nat.factorial, Nat.card_congr Multiplicative.toAdd]
      have hd := (c.first ⊔ c.second : Subgroup d.offenderGroup).card_subgroup_dvd_card
      rw [hc, Nat.card_congr eN.toEquiv, Nat.card_perm, Nat.card_fin] at hd
      rcases hn with rfl | rfl <;> norm_num at hd

/-- The source extension clause and two-perfectness put Y_F in the actual F*. -/
theorem first_le_source_fitting
    (c : QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup)) :
    d.YF.map coreProjection ≤ (generalizedFitting d.offenderGroup).map d.offenderGroup.subtype := by
  have hp : IsPGroup 2 (d.offenderGroup ⧸ generalizedFitting d.offenderGroup) := by
    have full (ht : generalizedFitting d.offenderGroup = ⊤) :
        IsPGroup 2 (d.offenderGroup ⧸ generalizedFitting d.offenderGroup) := by
      let : Subsingleton (d.offenderGroup ⧸ (⊤ : Subgroup d.offenderGroup)) :=
        QuotientGroup.subsingleton_quotient_top
      let : Subsingleton (d.offenderGroup ⧸ generalizedFitting d.offenderGroup) :=
        (QuotientGroup.quotientMulEquivOfEq ht).injective.subsingleton
      exact IsPGroup.of_subsingleton _ _
    cases c.clause_one with
    | irreducible _ _ _ _ he =>
      rcases he with ht | ⟨hs, _⟩
      · exact full ht
      · let T : Sylow 2 d.offenderGroup := Classical.choice inferInstance
        exact isPGroup_quotient_of_sup_eq_top _ _ T.isPGroup' (hs T)
    | doubleThree _ ht _ _ _ => exact full ht
    | naturalDual _ _ ht _ => exact full ht
    | repeatedNatural _ _ _ _ _ ht _ => exact full ht
  let f : d.YF →* d.offenderGroup :=
    { toFun y := ⟨coreProjection y, d.first_image_le (mem_map_of_mem coreProjection y.property)⟩
      map_one' := by ext; exact map_one coreProjection
      map_mul' a b := by ext; exact map_mul coreProjection (a : H) (b : H) }
  have hr := map_pResidual_le 2 f
  rw [(pResidual_eq_top_iff 2 d.YF).mpr d.first_perfect] at hr
  have hL : pResidual 2 d.offenderGroup ≤ generalizedFitting d.offenderGroup :=
    sInf_le ⟨inferInstance, hp⟩
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨f ⟨y, hy⟩, hL (hr (mem_map_of_mem f (mem_top _))), rfl⟩

/-- The full-offender branch needs no extension of the action across a new coset:
B.5.1 supplies natural coordinates for the whole acting symmetric group. -/
theorem naturalSection_of_full_offender {n : ℕ} (hn : n = 6 ∨ n = 7)
    (e : coreQuotient H ≃* Equiv.Perm (Fin n))
    (hN : d.offenderGroup = ⊤) (h : SourceAlternative d.offenderAction) :
    Nonempty (NaturalSection d n) := by
  obtain ⟨hq, ⟨c⟩⟩ := quasisimple_of_full_offender d hn e hN h
  let eN := ((MulEquiv.subgroupCongr hN).trans topEquiv).trans e
  obtain ⟨a⟩ := outer_natural_of_symmetric d.offenderAction hn eN hq c
  exact ⟨{
    component := (generalizedFitting d.offenderGroup).map d.offenderGroup.subtype
    first_le := first_le_source_fitting d c
    sectionData := fullSection
      (quotientAction V d.centralizer_isTwoGroup d.core_centralizes) hN c.sectionData
    natural := fullSectionEquiv
      (quotientAction V d.centralizer_isTwoGroup d.core_centralizes) hN c.sectionData a }⟩

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation
