module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Binary.Intersection
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Binary.Escape
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Binary.Parabolic
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Binary.RootAction

/-!
# The complete binary local alternative in E.6.8(2)

The actual local intersection is a Borel or a maximal parabolic, and equals
C_L(V). The Borel branch is complete: corank two supplies a strict
U < A < V with corank one and escaping C_L(A); corank one retains the
actual A₆ identification. In the maximal-parabolic branch the action has
corank one and is identified with the action of a literal matrix root subgroup
of full Sp₄(2) on Sp₄(2)′.

The source Sylow arrangement already proves the subgroup split at parameter
one, so the explicit Borel-containment witness supplied by the parent is not
needed in this endpoint. The decomposition clause applies only when n > 1.

Source: Aschbacher–Smith, E.6.8(2), printed pp.247–248 (PDF pp.258–259).
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- Every clause of the binary symplectic alternative, with the parent's
explicit Borel-containment input. The proof is uniform in the class K and
therefore applies in particular to the full known-simple catalogue. -/
theorem binary_alternative (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : SymplecticDerivedModel L 1)
    (_hB : ∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B) :
    SymplecticAlternative M V U L 1 := by
  rcases binary_intersection_cases h earlier hU hL hm with hb | hp
  · exact binary_borel_alternative h earlier hU hL hm hb
  · exact ⟨hm, fixedSpace_corank_le hU.1 hL.1, by omega,
      Or.inr ⟨hp, binary_parabolic_root_action h earlier hU hL hm hp,
        binary_parabolic_actionCorank_one h earlier hU hL hm hp⟩⟩

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic
