module

public import CFSG.Quasithin.MainConverse.AlternatingSections.SmallDegrees
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# Proper simple sections of the actual commutator of PSp₄(2)

The faithful six-letter polar representation identifies the symplectic
matrix group with S₆. The proved quotient and commutator comparisons then
identify the actual carrier PSp₄(2)′ with A₆. Dickson's theorem, via the
proved PSL₂(9) ≃ A₆ comparison, shows that its proper simple sections are
prime cyclic or A₅. We compose these actual equivalences throughout.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Main
Hypothesis 0.1.1(K) and Theorem 0.1.2(1), printed p.4, repeated on p.482;
Huppert, *Endliche Gruppen I*, II.8.27. This uses the commutator of the
central quotient, as in `ClassificationModels/Families.lean`, and does not
replace the small derived carrier by a family label.

Only the inclusion in the full known-simple catalogue remains explicit.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.KnownSimple
open Theory.SpecificGroups.SymplecticFour.Binary

/-- The two explicit alternatives for any proper simple section. -/
public theorem psp4_two_derived_proper_simple_section
    {G : Type*} [Group G]
    (e : G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))
    (U : Subgroup G) (hU : U ≠ ⊤)
    {S : Type*} [Group S] [IsSimpleGroup S] (V : Subgroup U)
    (f : V →* S) (hf : Function.Surjective f) :
    IsPrimeCyclicCarrier S ∨ Nonempty (S ≃* alternatingGroup (Fin 5)) :=
  alternatingSix_proper_simple_section
    (e.trans projectiveDerivedEquivAlternatingSix) U hU V f hf

/-- The normal subgroup is normal in `V`, with no ambient-normality requirement. -/
public theorem psp4_two_derived_proper_simple_quotient
    {G : Type*} [Group G]
    (e : G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))
    (U : Subgroup G) (hU : U ≠ ⊤) (V : Subgroup U)
    (N : Subgroup V) [N.Normal] [IsSimpleGroup (V ⧸ N)] :
    IsPrimeCyclicCarrier (V ⧸ N) ∨ Nonempty ((V ⧸ N) ≃* alternatingGroup (Fin 5)) :=
  psp4_two_derived_proper_simple_section e U hU V
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- Every proper simple section lies in the already constructed carriers. -/
public theorem psp4_two_derived_properK_constructed
    {G : Type*} [Group G]
    (e : G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) :
    HasProperKSubgroups IsConstructedCarrier G := by
  intro U hU S _ hS V f hf
  let := hS
  rcases psp4_two_derived_proper_simple_section e U hU V f hf with hc | ha
  · exact .cyclic hc
  · exact .alternating 5 (by decide) ha

/-- The small derived symplectic proper-K clause, with only catalogue inclusion. -/
public theorem psp4_two_derived_properK_of_catalogue
    {G : Type*} [Group G] [Finite G] {K : GroupClass}
    (hK : ∀ (S : Type _) [Group S] [Finite S] [IsSimpleGroup S],
      IsConstructedCarrier S → K S)
    (e : G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) :
    HasProperKSubgroups K G :=
  alternatingSix_properK_of_catalogue hK (e.trans projectiveDerivedEquivAlternatingSix)

end CFSG.Quasithin.MainConverse
