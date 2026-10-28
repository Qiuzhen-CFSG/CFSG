module
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# The symmetric-five action in the M₁₂ contradiction

An actual A₅ subgroup of C₂×S₅ is its derived subgroup: perfectness gives
containment and equal orders give equality. A transposition therefore induces
an outer automorphism on this subgroup. We transport this conclusion through
the supplied isomorphism of the full centralizer, keeping its action on the
actual embedded subgroup. This is the final elementary obstruction in the
centerless branch; identifying the M₁₂ centralizers is a separate input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of Lemma 16.4.11(2), printed p.1193.
-/

@[expose] public section
namespace Theory.SymmetricFiveProduct
open Subgroup Equiv
open scoped commutatorElement
abbrev A5 := alternatingGroup (Fin 5)
abbrev C2 := Multiplicative (ZMod 2)
abbrev InnerCentralizerModel := C2 × Perm (Fin 5)

private theorem perfect_a5 : Group.IsPerfect A5 :=
  ⟨commutator_alternatingGroup_eq_top (by simp)⟩

private theorem derived_model : commutator InnerCentralizerModel =
    (⊥ : Subgroup C2).prod (alternatingGroup (Fin 5)) := by
  change ⁅(⊤ : Subgroup InnerCentralizerModel), ⊤⁆ = _
  rw [← Subgroup.top_prod_top, commutator_prod_prod]
  change (commutator C2).prod (commutator (Perm (Fin 5))) = _
  rw [commutator_eq_bot, alternatingGroup.commutator_perm_eq (by simp)]

private theorem model_factor_card :
    Nat.card ((⊥ : Subgroup C2).prod (alternatingGroup (Fin 5))) = Nat.card A5 := by
  rw [Nat.card_congr (Subgroup.prodEquiv (⊥ : Subgroup C2) (alternatingGroup (Fin 5))).toEquiv,
    Nat.card_prod, card_bot, one_mul]

/-- A transposition in S₅ acts outerly on its actual alternating subgroup. -/
private theorem transposition_outer :
    ∀ a : A5, ∃ b : A5,
      (Equiv.swap (0 : Fin 5) 1) * (b : Perm (Fin 5)) * (Equiv.swap (0 : Fin 5) 1)⁻¹ ≠
        (a : Perm (Fin 5)) * b * (a : Perm (Fin 5))⁻¹ := by
  decide +kernel

/-- For any embedded A₅ in C₂×S₅, some element of the full product acts
non-innerly. The embedding is forced to be the derived subgroup by perfectness
and cardinality; no arbitrary identification of actions is assumed. -/
theorem product_has_outer_actor {G : Type*} [Group G] [Finite G]
    {C A : Subgroup G} (hAC : A ≤ C)
    (eC : C ≃* InnerCentralizerModel) (eA : A ≃* A5) :
    ∃ x ∈ C, ¬ ∃ a ∈ A, ∀ b ∈ A, x * b * x⁻¹ = a * b * a⁻¹ := by
  let f : A →* InnerCentralizerModel := eC.toMonoidHom.comp (inclusion hAC)
  have hf : Function.Injective f := eC.injective.comp (inclusion_injective hAC)
  let : Group.IsPerfect A5 := perfect_a5
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := eA.symm.toMonoidHom) eA.symm.surjective
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hle : f.range ≤ (⊥ : Subgroup C2).prod (alternatingGroup (Fin 5)) := by
    rw [← derived_model, ← Subgroup.commutator_eq_self (H := f.range)]
    exact commutator_mono le_top le_top
  have heq : f.range = (⊥ : Subgroup C2).prod (alternatingGroup (Fin 5)) := by
    apply eq_of_le_of_card_ge hle
    rw [model_factor_card, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    exact (Nat.card_congr eA.toEquiv).ge
  let t : InnerCentralizerModel := (1, Equiv.swap (0 : Fin 5) 1)
  let x := eC.symm t
  refine ⟨x, x.property, ?_⟩
  rintro ⟨a, ha, hact⟩
  have haf : f ⟨a, ha⟩ ∈ (⊥ : Subgroup C2).prod (alternatingGroup (Fin 5)) :=
    heq ▸ (MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩)
  let a₅ : A5 := ⟨(f ⟨a, ha⟩).2, haf.2⟩
  obtain ⟨b₅, hb₅⟩ := transposition_outer a₅
  have hb : ((1 : C2), (b₅ : Perm (Fin 5))) ∈ f.range := by
    rw [heq]
    exact ⟨mem_bot.mpr rfl, b₅.property⟩
  obtain ⟨b, hb⟩ := hb
  have hact' : x * (inclusion hAC b) * x⁻¹ =
      (inclusion hAC ⟨a, ha⟩) * inclusion hAC b * (inclusion hAC ⟨a, ha⟩)⁻¹ :=
    Subtype.ext (hact b b.property)
  have hh := congrArg (fun c : C => (eC c).2) hact'
  simp only [map_mul, map_inv, x, eC.apply_symm_apply] at hh
  change t.2 * (f b).2 * t.2⁻¹ = (f ⟨a, ha⟩).2 * (f b).2 * (f ⟨a, ha⟩).2⁻¹ at hh
  rw [hb] at hh
  exact hb₅ hh

end Theory.SymmetricFiveProduct
