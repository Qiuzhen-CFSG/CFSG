module

public import Theory.SpecificGroups.Held.RankOneLocalPair
public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.Held
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Solvable
public import CFSG.Quasithin.Defs

/-!
# The Held local pair as an E-generation input

The solvable member of the actual pair satisfies E.1.13. Thus the existing
two-member generating-family argument needs only the intrinsic rank-one
bound for the maximal member. The genuine SQTK hypothesis restricts to
that member; its PSL₃(2) quotient condition uses its own two-core.

The final adapter constructs the pair through the faithful automorphism
range of the original group. Both concrete overgroup constructions and
the maximal member's E-generation bound remain explicit prerequisites.
This is conditional assembly, not a proof of source E.1.14(4).

Source: Aschbacher--Smith E.1.12--14, refs/quasithin.pdf, printed p.214.
-/

public section

namespace CFSG.Quasithin.ChapterE
open Theory.GroupTheory Held.RankOneLocalPair

universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}

/-- E.1.13 supplies the second member's bound from actual solvability. -/
theorem held_generatingFamily_of_local_pair (T : Sylow 2 G) (P B : Subgroup G)
    (hpair : IsLocalPair (T : Subgroup G) P B) (hgenP : IsEGenerated 1 P) :
    sSup ({P, B} : Set (Subgroup G)) = ⊤ ∧
      ∀ H ∈ ({P, B} : Set (Subgroup G)),
        (T : Subgroup G) ≤ H ∧ IsEGenerated 1 H := by
  let := hpair.solvable
  exact held_pair_rankOne_generatingFamily T P B hpair.maximal hpair.card
    hpair.nine_dvd hpair.sylow_le_first hpair.sylow_le_second hgenP
    isEGenerated_one_of_solvable

/-- The conditional source adapter retains the original Sylow group, actual
component equivalence and genuine SQTK hypothesis. The independent local
constructions and PSL₃(2) rank-one bound must be supplied by their owners. -/
theorem held_generatingFamily_of_automorphism_overgroups
    [IsSimpleGroup (generalizedFitting G)]
    (hSQTK : IsSQTK K G) (e : generalizedFitting G ≃* Held.He)
    (T : Sylow 2 G) (hgen : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hmax : MaximalOvergroups) (hsol : SolvableOvergroups)
    (hlocal : ∀ P : Subgroup G, IsSQTK K P →
      HasPSL3TwoCoreQuotient P → IsEGenerated 1 P) :
    ∃ P B : Subgroup G, IsLocalPair (T : Subgroup G) P B ∧
      sSup ({P, B} : Set (Subgroup G)) = ⊤ ∧
      ∀ H ∈ ({P, B} : Set (Subgroup G)),
        (T : Subgroup G) ≤ H ∧ IsEGenerated 1 H := by
  obtain ⟨P, B, hpair⟩ := exists_of_automorphism_overgroups hmax hsol e T hgen
  exact ⟨P, B, hpair, held_generatingFamily_of_local_pair T P B hpair
    (hlocal P (hSQTK.subgroup P) hpair.quotient)⟩

end CFSG.Quasithin.ChapterE
