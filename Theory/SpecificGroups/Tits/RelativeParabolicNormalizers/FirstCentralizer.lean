module

public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.FirstCentralizer.Certificate
public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers
public import Theory.SpecificGroups.Tits.ReeLocalBlockOrders

/-!
# The first Tits parabolic is the full r5 centralizer

The first parabolic already centralizes r5. The certified ambient coset
equations write an arbitrary element as an R₁ element times one of the
specified representatives. Transport through the checked Parrott–Atlas
isomorphism and cancel the first factor. If the original element centralizes
r5, the representative does too; the pointwise certificate then forces its
word to be empty. This proves the reverse inclusion.

Consequently every automorphism preserving the marked Sylow subgroup
preserves the first parabolic, since it fixes r5. Neither an intrinsic
two-core order nor a construction of the full automorphism group is used.

Source: Parrott, *A Characterization of the Tits' Simple Group* (1972),
pp.672,683–684 (the correspondence z ↔ r5); application:
Aschbacher–Smith 2.3.9(7), printed p.526.
-/

namespace Tits.RelativeParabolicNormalizers

open Subgroup Theory.GroupTheory.CosetEnumeration

private theorem mapped_eval (w : Word ParrottGenerator) :
    (parrottFiniteImageEquiv (eval parrottGenerator w)).val =
      eval Atlas1600ParrottData.permutation w := by
  let f := atlas1600Subgroup.subtype.comp parrottFiniteImageEquiv.toMonoidHom
  have hgen (a : ParrottGenerator) : f (parrottGenerator a) =
      Atlas1600ParrottData.permutation a := by
    change (parrottFiniteImageEquiv (parrottGenerator a)).val = _
    rw [parrottFiniteImageEquiv_generator, atlas1600ParrottAssignment_val]
  change f (eval parrottGenerator w) = eval Atlas1600ParrottData.permutation w
  simp only [eval, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  cases a with
  | mk a b => cases b <;> simp [letterValue, hgen]

set_option maxRecDepth 30000 in
private theorem concrete_covers (x : ParrottGroup) :
    ∃ h : parrottR1Subgroup, ∃ i : Fin 1755,
      x = h.val * representative parrottGenerator R1Certificate.input (R1Certificate.index i) := by
  let C : ParrottR1CosetCover := {
    rep := fun i => representative parrottGenerator R1Certificate.input (R1Certificate.index i)
    initial := R1Certificate.initial
    initial_eq := by simp [representative, R1Certificate.initial_index, R1Certificate.model.zero]
    step := fun a => tablePermutation R1Certificate.table R1Certificate.inverse_table (a, true)
    transition := fun i a => by
      simpa only [Fact.Valid, Related, eval_singleton, letterValue, ↓reduceIte,
        tablePermutation, Equiv.coe_fn_mk] using R1Certificate.edges i a }
  exact C.covers x

/-- The full centralizer of the marked central involution is the first parabolic. -/
public theorem first_eq_centralizer :
    ExceptionalParabolics.first = centralizer {atlas1600R5} := by
  apply le_antisymm ExceptionalParabolics.first_le_centralizer
  intro x hx
  obtain ⟨h, i, he⟩ := concrete_covers (parrottFiniteImageEquiv.symm x)
  have hxform : x = parrottFiniteImageEquiv h.val * parrottFiniteImageEquiv
      (representative parrottGenerator R1Certificate.input (R1Certificate.index i)) := by
    rw [← map_mul, ← he, MulEquiv.apply_symm_apply]
  have hh : parrottFiniteImageEquiv h.val ∈ ExceptionalParabolics.first := by
    rw [← ReeLocalBlockOrders.first_map]
    exact mem_map_of_mem _ h.property
  have hr : parrottFiniteImageEquiv
      (representative parrottGenerator R1Certificate.input (R1Certificate.index i)) ∈
      centralizer {atlas1600R5} := by
    apply (mul_mem_cancel_left (ExceptionalParabolics.first_le_centralizer hh)).mp
    rwa [← hxform]
  have hv : atlas1600R5.val =
      Atlas1600ParrottData.s1Perm * Atlas1600ParrottData.s5Perm ^ 2 := by
    rw [atlas1600R5_eq]
    change (atlas1600ParrottAssignment .s1).val * (atlas1600ParrottAssignment .s5).val ^ 2 = _
    simp only [atlas1600ParrottAssignment_val, Atlas1600ParrottData.permutation]
  have hc := congrArg (fun g : Atlas1600Group => g.val)
    (mem_centralizer_singleton_iff.mp hr)
  change (parrottFiniteImageEquiv _).val * atlas1600R5.val =
    atlas1600R5.val * (parrottFiniteImageEquiv _).val at hc
  simp only [representative, mapped_eval, hv] at hc
  have hempty := FirstCentralizerCertificate.representative_word_eq_nil_of_commute
    (R1Certificate.index i) hc
  rw [representative, hempty, eval_nil, map_one, mul_one] at hxform
  exact hxform.symm ▸ hh

/-- Preserving the marked Sylow subgroup intrinsically preserves the first parabolic. -/
public theorem first_stabilized (β : MulAut Atlas1600Group)
    (hβ : atlas1600SylowTwoSubgroup.map β.toMonoidHom = atlas1600SylowTwoSubgroup) :
    ExceptionalParabolics.first.map β.toMonoidHom = ExceptionalParabolics.first :=
  first_stabilized_of_centralizer first_eq_centralizer β hβ

end Tits.RelativeParabolicNormalizers
