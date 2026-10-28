module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.Obstruction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.ModelInputs
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.ActorGeometry

/-!
# The two remaining outer-actor cases for odd PSU₃ generation

The proved action and intersection bounds reduce a large outer-family
obstruction to an actor of order four with inner intersection of order two,
or an actor of order eight with inner intersection of order four. The
reduction uses an actual family member, without replacing it by its inner
intersection. `ActorGeometry` also constructs the outer involution, identifies
its actual fixed group, and embeds the inner actor in that group.

The two local exclusions below remain explicit inputs. In particular this
module does not yet prove the unconditional outer branch of E.1.14(7).
Its final assembly must construct the local E-members, with their intrinsic
Sylow intersections, radical quotients and corrected local tau, and derive
the contradiction to the proper obstruction overgroup in both cases.

Source: Aschbacher--Smith, E.1.14(7), printed p.214, referring to
Aschbacher, *GF(2)-representations of finite groups* (1982), Lemma 4.11.
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Conditional assembly of the two cardinal cases. The local exclusions
are genuine remaining premises, not consequences asserted by this theorem. -/
theorem no_large_obstruction_of_outer_actor_cases
    [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (d : LargeFamilyObstruction T)
    (houter : ∀ A ∈ d.family, A ≤ (T : Subgroup G) → A ≠ ⊥ →
      ¬ A ≤ generalizedFitting G)
    (hfour : ∀ A ∈ d.family, A ≤ (T : Subgroup G) → A ≠ ⊥ →
      Nat.card A = 4 → Nat.card (A ⊓ generalizedFitting G : Subgroup G) = 2 → False)
    (height : ∀ A ∈ d.family, A ≤ (T : Subgroup G) → A ≠ ⊥ →
      Nat.card A = 8 → Nat.card (A ⊓ generalizedFitting G : Subgroup G) = 4 → False) :
    False := by
  obtain ⟨A, hA, hAT, hne, hcases, _⟩ :=
    OuterFamilies.exists_large_outer_actor hp ho hmodel hLT d houter
  rcases hcases with ⟨hcard, hinter⟩ | ⟨hcard, hinter⟩
  · exact hfour A hA hAT hne hcard hinter
  · exact height A hA hAT hne hcard hinter

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
