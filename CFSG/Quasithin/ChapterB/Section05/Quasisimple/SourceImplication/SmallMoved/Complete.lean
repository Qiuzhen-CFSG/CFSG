module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.SmallMoved.TripleSix.Exclusion

/-!
# The complete small-moved B.5 source sieve

The triple-cover A6 exclusion discharges the last case of the faithful
irreducible catalogue. Together with the two-summand obstruction, every B.5.1
row now gives Irr⁺ on the original moved space and precisely one of the four
group families in 13.7.15(1). All central quotient actions remain literal.

Source: Aschbacher–Smith 13.7.15(1–2), printed pp.943–944.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The complete irreducible actor sieve, including the covered-A6 row. -/
theorem irreducible_actor_of_plane {A L : Subgroup G}
    (hf : Function.Injective ρ) (hA : IsBestOffender ρ A)
    (hd : Module.finrank (ZMod 2) (moved ρ A) ≤ 2)
    (hc : SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ)) :
    ActorList L := by
  rcases irreducible_actor_or_triple_of_plane ρ hf hA hd hc with hg | ht
  · exact hg
  · obtain ⟨hgen,⟨a⟩⟩ := ht
    exact (TripleSix.not_plane hf (hA.isOffender ρ) (hgen ▸ hA.le_offenderSubgroup ρ) hd a).elim

/-- The whole original B.5.1 row has one of the four source actor families. -/
theorem source_actor_of_plane {A L : Subgroup G}
    (hA : IsOffender ρ A) (hd : Module.finrank (ZMod 2) (moved ρ A) ≤ 2)
    (s : MovedSection ρ L)
    (hc : SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s) : ActorList L := by
  rcases source_actor_or_triple_of_plane ρ hA hd s hc with hg | ht
  · exact hg
  · obtain ⟨hf,hgen,⟨a⟩,C,_,hC,hdC⟩ := ht
    exact (TripleSix.not_plane hf (hC.isOffender _)
      (hgen ▸ hC.le_offenderSubgroup _) hdC a).elim

/-- Both conclusions on the actual component and actual moved subspace. -/
theorem source_irrPlus_and_actor_of_plane {A L : Subgroup G} [IsQuasisimple L]
    (hA : IsOffender ρ A) (hd : Module.finrank (ZMod 2) (moved ρ A) ≤ 2)
    (s : MovedSection ρ L)
    (hc : SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s) :
    IsIrrPlus ρ L (moved ρ L) ∧ ActorList L :=
  ⟨source_irrPlus_of_plane ρ hA hd s hc, source_actor_of_plane ρ hA hd s hc⟩
end CFSG.Quasithin.ChapterB.QuasisimpleSource.SmallMoved
