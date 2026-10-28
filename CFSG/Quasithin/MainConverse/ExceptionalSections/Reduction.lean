module

public import CFSG.Quasithin.MainConverse.SolvableSections
public import Theory.SpecificGroups.Triality.StandardModel
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2
public import Mathlib.Order.Atoms.Finite

/-!
# Reductions for proper simple sections of exceptional groups

Condition K in Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2 (printed p.4), repeated on p.482, concerns every simple quotient
of every subgroup inside a proper subgroup. The normal subgroup used for a
quotient is normal in that subgroup, rather than in the ambient simple group.

Move such a section along the actual model isomorphism and into a maximal
subgroup. Solvable simple targets are prime cyclic. A nonsolvable simple
section survives removal of a solvable normal kernel, by the normal-image
alternative. The first isomorphism theorem lets a classification of quotients
in the concrete model's universe handle targets in arbitrary universes.

The section list names independently constructed carriers. Besides the base
constructed catalogue, it includes genuine graph-field triality groups and the
ATLAS J₂ permutation carrier, both absent from that base catalogue. This is a
partial list of known carriers, not a definition of the full class K.

`properK_of_maximal_sections` is conditional on the actual maximal-subgroup
section calculation. These reductions do not assert that calculation for any
exceptional family; each family theorem must prove it before source assembly.
-/

@[expose] public section

universe u v w

namespace CFSG.Quasithin.MainConverse.ExceptionalSections

open CFSG.KnownSimple

/-- Concrete known carriers available for the exceptional section calculations.
Every constructor contains an actual model isomorphism, directly or through
the imported catalogue. Exhaustion is a separate theorem. -/
inductive IsSectionCarrier (S : Type u) [Group S] : Prop
  | constructed (h : IsConstructedCarrier S)
  | triality (h : Triality.Standard.IsTrialityGroup S)
  | jankoTwo (h : Nonempty (S ≃* Sporadic.LeechRelated.J2.Carrier))

/-- The carrier list is invariant under actual isomorphisms across universes. -/
theorem IsSectionCarrier.of_mulEquiv {G : Type u} {H : Type v} [Group G] [Group H]
    (h : IsSectionCarrier H) (e : G ≃* H) : IsSectionCarrier G := by
  cases h with
  | constructed h => exact .constructed (h.of_mulEquiv e)
  | triality h => exact .triality (h.of_mulEquiv e)
  | jankoTwo h => exact .jankoTwo (h.map fun a => e.trans a)

/-- A nontrivial quotient of a simple carrier is the same concrete carrier. -/
theorem IsSectionCarrier.of_surjective {G : Type v} {S : Type u}
    [Group G] [Group S] [IsSimpleGroup G] [Nontrivial S]
    (h : IsSectionCarrier G) (f : G →* S) (hf : Function.Surjective f) :
    IsSectionCarrier S := by
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · obtain ⟨s, hs⟩ := exists_ne (1 : S)
      obtain ⟨g, rfl⟩ := hf s
      have hg : g ∈ f.ker := by rw [ht]; trivial
      exact False.elim (hs hg)
  exact h.of_mulEquiv (MulEquiv.ofBijective f ⟨hinj, hf⟩).symm

/-- Move a section inside a proper subgroup to a maximal subgroup of the model. -/
theorem section_in_maximal_subgroup {G : Type u} {H : Type v} {S : Type w}
    [Group G] [Group H] [Group S] [Finite H] (e : G ≃* H)
    (U : Subgroup G) (hU : U ≠ ⊤) (V : Subgroup U)
    (f : V →* S) (hf : Function.Surjective f) :
    ∃ M : Subgroup H, IsCoatom M ∧
      ∃ W : Subgroup M, ∃ g : W →* S, Function.Surjective g := by
  have hproper : U.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    have hh := congrArg (Subgroup.map e.symm.toMonoidHom) ht
    apply hU
    simpa [Subgroup.map_map] using hh
  obtain ⟨M, hM, hUM⟩ :=
    (eq_top_or_exists_le_coatom (U.map e.toMonoidHom)).resolve_left hproper
  let a := Subgroup.equivMapOfInjective U e.toMonoidHom e.injective
  let i : U →* M := (Subgroup.inclusion hUM).comp a.toMonoidHom
  have hi : Function.Injective i := (Subgroup.inclusion_injective hUM).comp a.injective
  let b := Subgroup.equivMapOfInjective V i hi
  exact ⟨M, hM, V.map i, f.comp b.symm.toMonoidHom, hf.comp b.symm.surjective⟩

/-- No parity hypothesis is needed to remove a solvable normal kernel. -/
theorem nonsolvable_section_mod_solvable {G : Type v} {S : Type u}
    [Group G] [Group S] [IsSimpleGroup S]
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N]
    (hS : ¬ Group.IsSolvable S) (U : Subgroup G)
    (f : U →* S) (hf : Function.Surjective f) :
    ∃ W : Subgroup (G ⧸ N), ∃ g : W →* S, Function.Surjective g := by
  rcases Subgroup.simple_section_normal_or_quotient N U f hf with ⟨W, g, hg⟩ | h
  · exact False.elim (hS (Group.isSolvable_of_surjective (f := g) hg))
  · exact h

/-- A solvable outer quotient contributes no nonsolvable simple sections. -/
theorem nonsolvable_section_in_normal {G : Type v} {S : Type u}
    [Group G] [Group S] [IsSimpleGroup S]
    (N : Subgroup G) [N.Normal] [Group.IsSolvable (G ⧸ N)]
    (hS : ¬ Group.IsSolvable S) (U : Subgroup G)
    (f : U →* S) (hf : Function.Surjective f) :
    ∃ W : Subgroup N, ∃ g : W →* S, Function.Surjective g := by
  rcases Subgroup.simple_section_normal_or_quotient N U f hf with h | ⟨W, g, hg⟩
  · exact h
  · exact False.elim (hS (Group.isSolvable_of_surjective (f := g) hg))

/-- The remaining family calculation, restricted to nonabelian simple sections
of maximal subgroups. This predicate does not assert that calculation. -/
def NonabelianMaximalSections (H : Type v) [Group H] : Prop :=
  ∀ (M : Subgroup H), IsCoatom M →
    ∀ (S : Type u) [Group S] [IsSimpleGroup S], ¬ Group.IsSolvable S →
      ∀ (U : Subgroup M) (f : U →* S), Function.Surjective f → IsSectionCarrier S

/-- Classifying actual quotients in the model's universe suffices for targets in
any universe: use the first isomorphism theorem and transport the concrete model. -/
theorem NonabelianMaximalSections.changeUniverse {H : Type v} [Group H]
    (h : NonabelianMaximalSections.{v, v} H) : NonabelianMaximalSections.{u, v} H := by
  intro M hM S _ hS hns U f hf
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  let : IsSimpleGroup (U ⧸ f.ker) := e.isSimpleGroup
  have hnq : ¬ Group.IsSolvable (U ⧸ f.ker) := by
    intro hq
    let := hq
    exact hns (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  exact (h M hM (U ⧸ f.ker) hnq U (QuotientGroup.mk' f.ker)
    (QuotientGroup.mk'_surjective f.ker)).of_mulEquiv e.symm

/-- Conditional assembly: the family classification remains an explicit input. -/
theorem properK_of_maximal_sections {G : Type u} {H : Type v}
    [Group G] [Group H] [Finite H] {K : GroupClass.{u}}
    (hK : ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S],
      IsSectionCarrier S → K S)
    (e : G ≃* H) (hsections : NonabelianMaximalSections.{v, v} H) :
    HasProperKSubgroups K G := by
  let : Finite G := Finite.of_injective e e.injective
  intro U hU S _ hS V f hf
  let := hS
  let : Finite S := Finite.of_surjective f hf
  apply hK S
  by_cases hsolv : Group.IsSolvable S
  · let := hsolv
    exact .constructed (.cyclic (primeCyclic_of_solvable_simple S))
  · obtain ⟨M, hM, W, g, hg⟩ := section_in_maximal_subgroup e U hU V f hf
    exact hsections.changeUniverse M hM S hsolv W g hg

end CFSG.Quasithin.MainConverse.ExceptionalSections
