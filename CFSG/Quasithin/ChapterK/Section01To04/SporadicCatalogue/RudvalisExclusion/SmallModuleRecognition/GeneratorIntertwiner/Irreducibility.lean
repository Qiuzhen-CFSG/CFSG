module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.RudvalisExclusion.StandardModule
public import Theory.SpecificGroups.Rudvalis.Model.Basic
public import Theory.Representation.CyclotomicPrimeCyclicity
public import Theory.Representation.Quotient

/-!
# Irreducibility of faithful binary Rudvalis modules of degree 28

The checked word `Rudvalis.w` has order 29. Since two has multiplicative order
28 modulo 29, its faithful action on a binary space of dimension 28 is
irreducible by the prime-order minimum-degree theorem. Consequently the
whole group acts irreducibly. In particular this proves irreducibility of
the literal ATLAS matrix action from any explicit carrier comparison.

This discharges the fixed-module irreducibility needed in the trace route to
the degree-28 case of Hiss--Malle's corrected Table 2, p.102. It does not
assume absolute irreducibility or the uniqueness asserted by that route.
The prime-order argument is the Singer argument underlying
Huppert--Blackburn, Finite Groups III, XI.3.10(a).
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion
namespace GeneratorIntertwiner
open Representation

private theorem orderOf_two_mod_twentyNine : orderOf (2 : ZMod 29) = 28 := by
  apply (orderOf_eq_iff (by decide : 0 < 28)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

/-- Faithfulness and degree 28 already force ordinary irreducibility;
no quasisimplicity or absolute-degree classification is needed. -/
theorem faithful_degree28_isIrreducible
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) Rudvalis.Model V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 28) :
    ρ.IsIrreducible := by
  let C := Subgroup.zpowers Rudvalis.w
  have hC : Nat.card C = 29 := by
    rw [Nat.card_zpowers, Rudvalis.orderOf_w]
  let : Fact (Nat.Prime 29) := ⟨by decide⟩
  let τ : Representation (ZMod 2) C V := ρ.comp C.subtype
  have hi : τ.IsIrreducible :=
    CyclotomicPrimeCyclicity.irreducible_of_prime_card hC (by decide)
      (by decide) τ (hf.comp C.subtype_injective)
      (by simpa only [ZMod.card, Nat.cast_ofNat, orderOf_two_mod_twentyNine] using hd.le)
  let := hi
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial τ
  refine ⟨fun U => ?_⟩
  let W : Subrepresentation τ :=
    ⟨U.toSubmodule, fun g _ hv => U.apply_mem_toSubmodule g.val hv⟩
  rcases eq_bot_or_eq_top W with h | h
  · left
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation τ => U.toSubmodule) h)
  · right
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation τ => U.toSubmodule) h)

/-- The particular pullback used in the generator-intertwiner contract is
irreducible, independently of the degree-window and trace calculations. -/
theorem pulledStandard_isIrreducible (e : Rudvalis.Model ≃* standardGroup) :
    Representation.IsIrreducible (standardRepresentation.comp e.toMonoidHom) :=
  faithful_degree28_isIrreducible (standardRepresentation.comp e.toMonoidHom)
    (standardRepresentation_injective.comp e.injective) finrank_space

/-- The literal fixed matrix action is irreducible whenever its comparison
with the permutation carrier is supplied. Generator markings are unnecessary. -/
theorem standardRepresentation_isIrreducible (e : Rudvalis.Model ≃* standardGroup) :
    standardRepresentation.IsIrreducible :=
  (irreducible_comp_surjective_iff e.toMonoidHom e.surjective standardRepresentation).mp
    (pulledStandard_isIrreducible e)

end GeneratorIntertwiner
end CFSG.Quasithin.ChapterK.SporadicCatalogue.RudvalisExclusion
