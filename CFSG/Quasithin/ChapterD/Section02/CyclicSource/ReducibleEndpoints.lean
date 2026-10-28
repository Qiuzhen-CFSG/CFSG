module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.LocalGeneration
public import Theory.Representation.CyclotomicPrimeCyclicity
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel.MinimalDegree

/-!
# Reducible endpoints of the literal cyclic source action

A reducible cyclic D.2.17 factor is either the four-dimensional S₃ action
or the inverted elementary nine action. Faithful cubic actions on a binary
plane and faithful quintic actions on a four-space are irreducible by their
minimal nondefining degree. The extraspecial kernel of order 27 is likewise
irreducible in degree six. The conclusion retains the original kernel,
generating involution and marked endpoint description.

Source: Aschbacher--Smith D.2.17 and 15.1.2, printed pp.188 and 1085.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.CyclicSource
universe u
variable {G V : Type u} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem irreducible_of_restriction (A : Subgroup G)
    (hi : IsIrreducible (ρ.comp A.subtype)) : IsIrreducible ρ := by
  have hn : Nontrivial V := by
    let := hi
    exact Subrepresentation.irreducible_module_nontrivial (ρ.comp A.subtype)
  let := hn
  refine ⟨fun S => ?_⟩
  let R : Subrepresentation (ρ.comp A.subtype) := {
    toSubmodule := S.toSubmodule
    apply_mem_toSubmodule := fun g v hv => S.apply_mem_toSubmodule g hv }
  rcases hi.eq_bot_or_eq_top R with h | h
  · have hh : S.toSubmodule = ⊥ :=
      congrArg (fun X : Subrepresentation (ρ.comp A.subtype) => X.toSubmodule) h
    exact Or.inl (Subrepresentation.toSubmodule_injective hh)
  · have hh : S.toSubmodule = ⊤ :=
      congrArg (fun X : Subrepresentation (ρ.comp A.subtype) => X.toSubmodule) h
    exact Or.inr (Subrepresentation.toSubmodule_injective hh)

private theorem dimension_of_card {n : ℕ} (hc : Nat.card (Multiplicative V) = 2 ^ n) :
    Module.finrank (ZMod 2) V = n := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  change 2 ^ Module.finrank (ZMod 2) V = 2 ^ n
  have hh : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact hh.symm.trans ((Nat.card_congr (Multiplicative.toAdd (α := V))).symm.trans hc)

/-- The reducible cyclic source factor is either the four-dimensional S3
module or the order-eighteen inverted E9 module. -/
theorem LocalGeneration.endpoints_of_not_irreducible (l : LocalGeneration ρ)
    (hf : Function.Injective ρ) (hi : ¬ IsIrreducible ρ) :
    letI := BinaryGroupAction.action ρ
    letI : Finite V := Module.finite_of_finite (ZMod 2)
    letI : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
    letI := l.normal
    (Section02.CyclicThreeEndpoint (V := Multiplicative V) l.kernel l.involution ∧
      Module.finrank (ZMod 2) V = 4) ∨
      Section02.ElementaryNineEndpoint (V := Multiplicative V) l.kernel l.involution := by
  let := BinaryGroupAction.action ρ
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let := l.normal
  rcases l.endpoints hf with h3 | h5 | h9 | h27
  · apply Or.inl
    refine ⟨h3,?_⟩
    rcases h3.dimensions with hd | hd
    · exfalso
      apply hi
      apply irreducible_of_restriction l.kernel
      have hc : Nat.card l.kernel = 3 := by
        obtain ⟨e⟩ := h3.kernel_equiv
        rw [Nat.card_congr e.toEquiv,Nat.card_congr (Multiplicative.toAdd (α := ZMod 3)),Nat.card_zmod]
        
      apply CyclotomicPrimeCyclicity.irreducible_of_prime_card (r := 3) hc
        (by decide) (by norm_num) (ρ.comp l.kernel.subtype) (hf.comp l.kernel.subtype_injective)
      norm_num only [ZMod.card,Nat.cast_ofNat]
      rw [BinaryPrimeDegree.orderOf_two_mod_three,dimension_of_card (n := 2) hd.1]
    · exact dimension_of_card (n := 4) hd.1
  · exfalso
    apply hi
    apply irreducible_of_restriction l.kernel
    have hc : Nat.card l.kernel = 5 := by
      obtain ⟨e⟩ := h5.kernel_equiv
      rw [Nat.card_congr e.toEquiv,Nat.card_congr (Multiplicative.toAdd (α := ZMod 5)),Nat.card_zmod]
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    apply CyclotomicPrimeCyclicity.irreducible_of_prime_card (r := 5) hc
      (by decide) (by norm_num) (ρ.comp l.kernel.subtype) (hf.comp l.kernel.subtype_injective)
    norm_num only [ZMod.card,Nat.cast_ofNat]
    rw [BinaryPrimeDegree.orderOf_two_mod_five,dimension_of_card (n := 4) h5.card_module]
  · exact Or.inr h9
  · exfalso
    apply hi
    apply irreducible_of_restriction l.kernel
    let := h27.kernel_extraspecial
    exact RankTwo.ExtraspecialModel.irreducible_of_faithful_six (ρ.comp l.kernel.subtype)
      (hf.comp l.kernel.subtype_injective) h27.card_kernel (dimension_of_card (n := 6) h27.card_module)
end CFSG.Quasithin.ChapterD.CyclicSource
