module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels.FixedSubgroup
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Models
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.SymplecticFour.Blocks
public import Theory.SpecificGroups.SymplecticFour.FieldComponent
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.SylowFixedComponents

/-!
# Nonbinary symplectic fixed components

`SymplecticDerivedModel` stores the derived carrier `Sp₄(F)'`; for a
nonbinary field root generation identifies it with the full matrix group.
The root-centralizer calculation constructs the natural extension of the
selected relative C-component over that same field, retaining the actual
SL₂ action on its central quotient.

The assembly still has two explicit mathematical inputs: diagram-preserving
semilinear automorphism classification and the root/c₂ involution table.
They give innerness of a Sylow-pointwise automorphism and exclude the c₂
case by solvability. These conditional theorems do not yet discharge those
two inputs from the source hypotheses.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, E.6.8(2) and
E.6.25, printed pp.247--250 and 256 (PDF pp.258--261 and 267).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterE.Section06.Components
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels

universe u
variable {G : Type u} [Group G] [Finite G]

/-! The first two lemmas retain the actual field and the actual matrix carrier. -/

omit [Finite G] in
theorem symplecticDerivedModel_full_equiv {J : Subgroup G} {n : ℕ}
    (hn : 1 < n) (hJ : SymplecticDerivedModel J n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 2 ^ n ∧ Nonempty (J ≃* Sp F) := by
  obtain ⟨_, F, hF, hfin, hcard, ⟨e⟩⟩ := hJ
  let _ := hF
  let _ := hfin
  let _ := EvenProjective.charTwo_of_card hcard
  have hq : 2 < Nat.card F := by
    rw [hcard]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) (by omega))
  exact ⟨F, hF, hfin, hcard,
    ⟨e.trans (derivedEquivFull_of_card_gt_two hq)⟩⟩

omit [Finite G] in
theorem symplecticDerivedModel_full_equiv_of_card
    {J : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] (hcard : Nat.card F = 2 ^ n)
    (e : J ≃* commutator (Sp F)) (hn : 1 < n) :
    Nonempty (J ≃* Sp F) := by
  have hq : 2 < Nat.card F := by
    rw [hcard]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) (by omega))
  exact ⟨e.trans (derivedEquivFull_of_card_gt_two hq)⟩

/-! A public version of the genuine natural-extension recognition route. -/

theorem isL2EvenBlock_of_naturalExtension
    {B : Type*} [Group B] [Finite B]
    {Q : Subgroup B} [Q.Normal]
    {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (d : NaturalExtension (F := F) Q)
    (hn : 1 < n) (hcard : Nat.card F = 2 ^ n) :
    ChapterC.IsL2EvenBlock B n := by
  have h := ChapterF.SymplecticFourRecognition.recognition d hn hcard
  refine ⟨hn, h.2.2.1, F, inferInstance, inferInstance, hcard, ?_, h.2.2.2⟩
  obtain ⟨e⟩ := h.2.2.2.quotient_iso
  exact ChapterF.GreenBook.LieModels.SymplecticFour.isPSL_of_specialLinearEquiv
    hcard e

/-- The field and natural module carried by an `L₂(2ⁿ)` block are actual
    witnesses in its definition. -/
theorem isL2EvenBlock_actual_natural_model
    {B : Type*} [Group B] [Finite B] {n : ℕ}
    (hB : ChapterC.IsL2EvenBlock B n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 2 ^ n ∧
      ChapterC.IsLinearBlockModel B
        (Representation.specialLinearNatural (k := F) 2) := by
  obtain ⟨_, _, F, hF, hfin, hcard, _, hmodel⟩ := hB
  exact ⟨F, hF, hfin, hcard, hmodel⟩

/-!
The following assembly is the exact point at which the intrinsic centralizer
calculation enters.  It takes a genuine natural extension of the selected
component over the *same* field as the ambient symplectic model; no family tag
or recognition conclusion is used in place of that witness.
-/

theorem fixed_cComponent_isL2EvenBlock_of_naturalExtension
    {J : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hcard : Nat.card F = 2 ^ n) (_eJ : J ≃* commutator (Sp F))
    (hn : 1 < n) (_a : MulAut J) (_ha : orderOf _a = 2)
    (_S : Sylow 2 J) (_hS : ∀ x ∈ (_S : Subgroup J), _a x = x)
    {B : Subgroup J} (_hBfix : B ≤ _a.fixedSubgroup)
    (_hB : (B.subgroupOf _a.fixedSubgroup).IsCComponent)
    {Q : Subgroup B} [Q.Normal]
    (d : NaturalExtension (F := F) Q) :
    ChapterC.IsL2EvenBlock B n := by
  exact isL2EvenBlock_of_naturalExtension d hn hcard

/-- Construct the actual extension of the selected relative C-component from
the two intrinsic model calculations. The field is the original model field;
normality of the kernel is only inside the selected component. -/
theorem fixed_cComponent_naturalExtension_of_model_calculations
    {J : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hcard : Nat.card F = 2 ^ n) (eJ : J ≃* commutator (Sp F))
    (hn : 1 < n) (a : MulAut J) (ha : orderOf a = 2)
    (S : Sylow 2 J) (hS : ∀ x ∈ (S : Subgroup J), a x = x)
    {B : Subgroup J} (hBfix : B ≤ a.fixedSubgroup)
    (hB : (B.subgroupOf a.fixedSubgroup).IsCComponent)
    (hclass : ∀ b : MulAut (Sp F), DiagramAutomorphisms.PreservesDiagram b →
      ∃ g : Sp F, ∃ σ : F ≃+* F,
        b = MulAut.conj g * DiagramAutomorphisms.fieldAutomorphism σ)
    (htable : ∀ g : Sp F, orderOf g = 2 →
      InvolutionTypes.IsRootElement g ∨
        IsPGroup 2 (centralizer ({g} : Set (Sp F)))) :
    B = a.fixedSubgroup ∧ ∃ (Q : Subgroup B) (_ : Q.Normal),
      Nonempty (NaturalExtension (F := F) Q) := by
  obtain ⟨e⟩ := symplecticDerivedModel_full_equiv_of_card hcard eJ hn
  exact InvolutionCentralizers.fixed_cComponent_naturalExtension_of_model_calculations
    hcard hn hclass htable e a ha S hS hBfix hB

/-- Recognition retains the original field's natural module, as well as the
source block parameter. The two model calculations remain explicit inputs. -/
theorem fixed_cComponent_model_of_calculations
    {J : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hcard : Nat.card F = 2 ^ n) (eJ : J ≃* commutator (Sp F))
    (hn : 1 < n) (a : MulAut J) (ha : orderOf a = 2)
    (S : Sylow 2 J) (hS : ∀ x ∈ (S : Subgroup J), a x = x)
    {B : Subgroup J} (hBfix : B ≤ a.fixedSubgroup)
    (hB : (B.subgroupOf a.fixedSubgroup).IsCComponent)
    (hclass : ∀ b : MulAut (Sp F), DiagramAutomorphisms.PreservesDiagram b →
      ∃ g : Sp F, ∃ σ : F ≃+* F,
        b = MulAut.conj g * DiagramAutomorphisms.fieldAutomorphism σ)
    (htable : ∀ g : Sp F, orderOf g = 2 →
      InvolutionTypes.IsRootElement g ∨
        IsPGroup 2 (centralizer ({g} : Set (Sp F)))) :
    ChapterC.IsL2EvenBlock B n ∧
      ChapterC.IsLinearBlockModel B
        (Representation.specialLinearNatural (k := F) 2) := by
  obtain ⟨_, Q, hQ, ⟨d⟩⟩ :=
    fixed_cComponent_naturalExtension_of_model_calculations
      hcard eJ hn a ha S hS hBfix hB hclass htable
  let := hQ
  exact ⟨isL2EvenBlock_of_naturalExtension d hn hcard,
    (ChapterF.SymplecticFourRecognition.recognition d hn hcard).2.2.2⟩

/-! Parameter comparison uses the actual block module cardinality. -/

theorem l2_parameter_eq_of_module_card
    {B : Type*} [Group B] [Finite B] {m n : ℕ}
    (hm : ChapterC.IsL2EvenBlock B m)
    (hmodule : Nat.card (ChapterC.BlockModule B) = 2 ^ (n * 2)) :
    m = n := by
  have hp : 2 ^ (m * 2) = 2 ^ (n * 2) := by
    exact hm.module_card.symm.trans hmodule
  have hexp : m * 2 = n * 2 := by
    exact Nat.pow_right_injective (by decide : 1 < 2) hp
  omega

/-! An `L₂(4)` witness fixes the original symplectic field parameter. -/

omit [Finite G] in
theorem symplecticDerivedModel_sp4_four_of_l2_four
    {J : Subgroup G} {B : Type*} [Group B] [Finite B] {n : ℕ}
    (hn : 1 < n) (hJ : SymplecticDerivedModel J n)
    (hBn : ChapterC.IsL2EvenBlock B n)
    (hB2 : ChapterC.IsL2EvenBlock B 2) :
    n = 2 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 4 ∧ Nonempty (J ≃* Sp F) := by
  have h2n : 2 = n := l2_parameter_eq_of_module_card
    (m := 2) (n := n) hB2 hBn.module_card
  have hn2 : n = 2 := h2n.symm
  obtain ⟨F, hF, hfin, hcard, hJfull⟩ :=
    symplecticDerivedModel_full_equiv hn hJ
  refine ⟨hn2, F, hF, hfin, ?_, ?_⟩
  · simpa [hn2] using hcard
  · exact hJfull

/-!
For the nonbinary carrier the ambient group is simple.  Consequently a proper
fixed subgroup cannot contain an ordinary component of the ambient group.  This
is the ordinary-component exclusion used after the relative block calculation.
-/

omit [Finite G] in
theorem no_ordinary_component_in_nonbinary_symplectic
    {J : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hcard : Nat.card F = 2 ^ n) (eJ : J ≃* commutator (Sp F))
    (hn : 1 < n) (a : MulAut J) (ha : orderOf a = 2)
    {B : Subgroup J} (hBfix : B ≤ a.fixedSubgroup)
    (hOrd : Theory.GroupTheory.IsComponentIn B (⊤ : Subgroup J)) : False := by
  let : IsSimpleGroup (commutator (Sp F)) :=
    Theory.SpecificGroups.SymplecticFour.FieldComponent.derived_isSimple
      (by omega) hcard
  let : IsSimpleGroup J :=
    (MulEquiv.isSimpleGroup_congr eJ).mpr
      (Theory.SpecificGroups.SymplecticFour.FieldComponent.derived_isSimple
        (by omega) hcard)
  have hsub : B.IsSubnormal := by
    have hsurj : Function.Surjective ((⊤ : Subgroup J).subtype) := by
      intro x
      exact ⟨⟨x, mem_top x⟩, rfl⟩
    simpa only [map_subgroupOf_eq_of_le hOrd.1] using
      hOrd.2.1.map hsurj
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup
      (G := J) (H := B) (inferInstance : IsSimpleGroup J) hsub with hb | ht
  · exact hOrd.ne_bot hb
  · have hBtop : B = ⊤ := ht
    have hfix_top : a.fixedSubgroup = ⊤ := by
      apply top_unique
      intro x _
      exact hBfix (hBtop ▸ (show x ∈ (⊤ : Subgroup J) from mem_top x))
    have haone : a = 1 := by
      ext x
      have hx : x ∈ a.fixedSubgroup := hfix_top ▸ mem_top x
      simpa using congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp hx)
    have horder : orderOf a = 1 := by rw [haone]; exact orderOf_one
    omega

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels
