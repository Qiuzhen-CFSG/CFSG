module

public import CFSG.Quasithin.MainConverse.SolvableSections
public import Theory.GroupTheory.SimpleSectionSolvableReduction

/-!
# Assembly reductions for the Mathieu proper-section calculation

It suffices to classify nonsolvable simple quotients of single proper
subgroups of a concrete model. Flattening a subgroup of a proper subgroup
still gives a proper subgroup; mapping it across the model equivalence
preserves properness. Solvable simple quotients are prime cyclic.

The quotient group may live in a different universe from the concrete
permutation model. All transport below uses actual multiplicative
equivalences. The catalogue-enlargement theorem separately uses finiteness
of the quotient to discharge the finite/simple guards on the inclusion.

Source: Aschbacher–Smith, Theorem 0.1.2(5) and condition K, printed pp. 4
and 482. These are conditional assembly lemmas, not the missing Mathieu
proper-subgroup classifications.
-/

namespace CFSG.Quasithin.MainConverse.MathieuSections

open CFSG.KnownSimple

universe u v

/-- Transport a classification of nonsolvable simple quotients of proper
model subgroups to the full proper-K condition, including nested subgroups. -/
public theorem properK_of_nonsolvable_simple_sections_of_equiv
    {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H)
    (hsections : ∀ (S : Type u) [Group S] [IsSimpleGroup S],
      ¬ Group.IsSolvable S → ∀ (U : Subgroup H), U ≠ ⊤ →
      ∀ (f : U →* S), Function.Surjective f → IsConstructedCarrier S) :
    HasProperKSubgroups IsConstructedCarrier G := by
  intro U hU S _ hS V f hf
  let := hS
  by_cases hsolv : Group.IsSolvable S
  · let := hsolv
    exact .cyclic (primeCyclic_of_solvable_simple S)
  · let W := V.map U.subtype
    have hW : W ≠ ⊤ := by
      intro hw
      exact hU (top_unique (hw ▸ Subgroup.map_subtype_le V))
    let a := Subgroup.equivMapOfInjective V U.subtype U.subtype_injective
    let b := Subgroup.equivMapOfInjective W e.toMonoidHom e.injective
    have heW : W.map e.toMonoidHom ≠ ⊤ := by
      intro hw
      have hh := congrArg (Subgroup.map e.symm.toMonoidHom) hw
      apply hW
      simpa [Subgroup.map_map] using hh
    exact hsections S hsolv (W.map e.toMonoidHom) heW
      (f.comp (a.trans b).symm.toMonoidHom) (hf.comp (a.trans b).symm.surjective)

/-- Enlarge the proved section list to the parent's full catalogue. -/
public theorem properK_of_constructed_sections {G : Type u} [Group G] [Finite G]
    {K : GroupClass.{u}}
    (hK : ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S],
      IsConstructedCarrier S → K S)
    (hG : HasProperKSubgroups IsConstructedCarrier G) : HasProperKSubgroups K G := by
  intro U hU S _ hS V f hf
  let := hS
  let : Finite S := Finite.of_surjective f hf
  exact hK S (hG U hU S hS V f hf)

/-- Once the numerator is a known simple carrier, its nontrivial quotient
has the same carrier, by an actual equivalence induced by the quotient map. -/
public theorem constructed_simple_quotient_of_simple
    {G : Type u} {S : Type v} [Group G] [IsSimpleGroup G]
    [Group S] [Nontrivial S] (hG : IsConstructedCarrier G)
    (f : G →* S) (hf : Function.Surjective f) : IsConstructedCarrier S := by
  exact hG.of_mulEquiv
    (MulEquiv.ofBijective f ⟨f.injective_of_surjective_of_simple hf, hf⟩).symm

end CFSG.Quasithin.MainConverse.MathieuSections
