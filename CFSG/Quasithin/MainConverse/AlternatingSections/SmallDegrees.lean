module

public import CFSG.Quasithin.MainConverse.SolvableSections
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import CFSG.Quasithin.MainConverse.AlternatingSections.SixSubgroups

/-!
# Simple sections of A₅ and A₆

Source: Aschbacher–Smith, Theorem 0.1.2(3), condition K, printed p.4,
repeated on p.482. K includes all known finite simple groups, not just the
alternating alternatives in the theorem. Sections mean arbitrary surjective
homomorphisms from actual subgroups; no normality in the ambient Aₙ is imposed.

The A₅ proper-subgroup calculation follows from the faithful coset action
and Sylow theory. Its proper simple sections are prime cyclic. A simple
quotient of A₅ itself is isomorphic to A₅, giving the whole K-group statement.
For A₆, Dickson's theorem and the checked PSL₂(9) ≃ A₆ comparison show
that proper subgroups are solvable or copies of A₅. The degree-eight and
degree-nine calculations remain separate. Inclusion in the complete
catalogue is explicit and must be discharged by the main converse assembly.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.KnownSimple

private theorem simple_surjection_injective {H S : Type*} [Group H] [Group S]
    [IsSimpleGroup H] [Nontrivial S] (f : H →* S) (hf : Function.Surjective f) :
    Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨s, hs⟩ := exists_ne (1 : S)
    obtain ⟨x, rfl⟩ := hf s
    exact hs (show f x = 1 from show x ∈ f.ker by rw [h]; trivial)

/-- The exact carriers of simple sections of A₅, including the full group. -/
public theorem alternatingFive_simple_section {G : Type*} [Group G]
    (e : G ≃* alternatingGroup (Fin 5)) {S : Type*} [Group S] [IsSimpleGroup S]
    (U : Subgroup G) (f : U →* S) (hf : Function.Surjective f) :
    IsPrimeCyclicCarrier S ∨ Nonempty (S ≃* alternatingGroup (Fin 5)) := by
  by_cases hU : U = ⊤
  · subst U
    let eU : (⊤ : Subgroup G) ≃* alternatingGroup (Fin 5) := Subgroup.topEquiv.trans e
    let : IsSimpleGroup (⊤ : Subgroup G) := eU.isSimpleGroup
    exact Or.inr
      ⟨(MulEquiv.ofBijective f ⟨simple_surjection_injective f hf, hf⟩).symm.trans eU⟩
  · let : Group.IsSolvable U := alternatingGroup.isSolvable_subgroup_of_equiv_five e U hU
    let : Group.IsSolvable S := Group.isSolvable_of_surjective (f := f) hf
    exact Or.inl (primeCyclic_of_solvable_simple S)

/-- All simple sections of A₅ belong to the constructed catalogue. -/
public theorem alternatingFive_isKGroup_constructed {G : Type*} [Group G]
    (e : G ≃* alternatingGroup (Fin 5)) : IsKGroup IsConstructedCarrier G := by
  intro S _ hS U f hf
  let := hS
  rcases alternatingFive_simple_section e U f hf with hc | ha
  · exact .cyclic hc
  · exact .alternating 5 (by decide) ha

/-- Every simple section of a proper subgroup of A₅ is actually prime cyclic. -/
public theorem alternatingFive_proper_simple_section {G : Type*} [Group G]
    (e : G ≃* alternatingGroup (Fin 5)) (U : Subgroup G) (hU : U ≠ ⊤)
    {S : Type*} [Group S] [IsSimpleGroup S] (V : Subgroup U)
    (f : V →* S) (hf : Function.Surjective f) : IsPrimeCyclicCarrier S := by
  let : Group.IsSolvable U := alternatingGroup.isSolvable_subgroup_of_equiv_five e U hU
  let : Group.IsSolvable S := Group.isSolvable_of_surjective (f := f) hf
  exact primeCyclic_of_solvable_simple S

/-- The source proper-K clause for A₅, with only catalogue inclusion explicit. -/
public theorem alternatingFive_properK_of_catalogue {G : Type*} [Group G] [Finite G]
    {K : GroupClass}
    (hK : ∀ (S : Type _) [Group S] [Finite S] [IsSimpleGroup S],
      IsConstructedCarrier S → K S)
    (e : G ≃* alternatingGroup (Fin 5)) : HasProperKSubgroups K G := by
  intro U hU S _ hS V f hf
  let := hS
  let : Finite S := Finite.of_surjective f hf
  exact hK S (.cyclic (alternatingFive_proper_simple_section e U hU V f hf))

/-- Proper simple sections of A₆ are prime cyclic or actual copies of A₅. -/
public theorem alternatingSix_proper_simple_section {G : Type*} [Group G]
    (e : G ≃* alternatingGroup (Fin 6)) (U : Subgroup G) (hU : U ≠ ⊤)
    {S : Type*} [Group S] [IsSimpleGroup S] (V : Subgroup U)
    (f : V →* S) (hf : Function.Surjective f) :
    IsPrimeCyclicCarrier S ∨ Nonempty (S ≃* alternatingGroup (Fin 5)) := by
  rcases alternatingSix_subgroup_solvable_or_altFive e U hU with hs | ha
  · let := hs
    let : Group.IsSolvable S := Group.isSolvable_of_surjective (f := f) hf
    exact Or.inl (primeCyclic_of_solvable_simple S)
  · obtain ⟨a⟩ := ha
    exact alternatingFive_simple_section a V f hf

/-- All simple sections of A₆ belong to the constructed catalogue. -/
public theorem alternatingSix_isKGroup_constructed {G : Type*} [Group G]
    (e : G ≃* alternatingGroup (Fin 6)) : IsKGroup IsConstructedCarrier G := by
  intro S _ hS U f hf
  let := hS
  by_cases hU : U = ⊤
  · subst U
    let eU : (⊤ : Subgroup G) ≃* alternatingGroup (Fin 6) := Subgroup.topEquiv.trans e
    let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup (⊤ : Subgroup G) := eU.isSimpleGroup
    exact .alternating 6 (by decide)
      ⟨(MulEquiv.ofBijective f ⟨simple_surjection_injective f hf, hf⟩).symm.trans eU⟩
  · rcases alternatingSix_subgroup_solvable_or_altFive e U hU with hs | ha
    · let := hs
      let : Group.IsSolvable S := Group.isSolvable_of_surjective (f := f) hf
      exact .cyclic (primeCyclic_of_solvable_simple S)
    · obtain ⟨a⟩ := ha
      let : IsSimpleGroup U := a.isSimpleGroup
      exact .alternating 5 (by decide)
        ⟨(MulEquiv.ofBijective f ⟨simple_surjection_injective f hf, hf⟩).symm.trans a⟩

/-- The source proper-K clause for A₆, with only catalogue inclusion explicit. -/
public theorem alternatingSix_properK_of_catalogue {G : Type*} [Group G] [Finite G]
    {K : GroupClass}
    (hK : ∀ (S : Type _) [Group S] [Finite S] [IsSimpleGroup S],
      IsConstructedCarrier S → K S)
    (e : G ≃* alternatingGroup (Fin 6)) : HasProperKSubgroups K G := by
  intro U hU S _ hS V f hf
  let := hS
  let : Finite S := Finite.of_surjective f hf
  apply hK S
  rcases alternatingSix_proper_simple_section e U hU V f hf with hc | ha
  · exact .cyclic hc
  · exact .alternating 5 (by decide) ha

end CFSG.Quasithin.MainConverse
