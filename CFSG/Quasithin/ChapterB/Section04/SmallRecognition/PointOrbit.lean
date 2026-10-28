module

public import CFSG.Quasithin.ChapterB.Section04.SmallRecognition.SourceActions
public import Theory.Representation.BinaryOrbitSpan.FifteenPoints

/-!
# The remaining point-stabilizer input for B.4.12(2)

For L₄(2) and A₇ the source identifies the odd-index subgroups with intrinsic
two-core quotient L₃(2), and proves that their coset actions are twice
transitive of degree fifteen. `FifteenPointStabilizerInput` states precisely
this remaining action calculation. The conditional assembly below applies
B.4.12(1) to the supplied spanning orbit and plane, and counts vectors to
obtain dimension four. It does not assert the subgroup classification.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma B.4.12(2), printed p.97.
-/

@[expose] public section

open scoped MatrixGroups
open Representation

namespace CFSG.Quasithin.ChapterB.SmallRecognition
universe u w

/-- The group-action calculation still required by B.4.12(2). It asks for
two-transitivity and orbit size, not the conclusion about the vector space. -/
def FifteenPointStabilizerInput : Prop :=
  ∀ {G : Type u} {V : Type w} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (v : V),
    (Nonempty (G ≃* PSL(4, ZMod 2)) ∨ Nonempty (G ≃* alternatingGroup (Fin 7))) →
    Odd (Nat.card (Set.range fun g => ρ g v)) →
    Nonempty (((vectorStabilizer ρ v) ⧸ pCore 2 (vectorStabilizer ρ v)) ≃*
      PSL(3, ZMod 2)) →
    PairTransitiveOrbit ρ v ∧ Nat.card (Set.range fun g => ρ g v) = 15

/-- The actual B.4.12(2) assembly, conditional on the independent subgroup
calculation. The action, orbit, and intrinsic two-core quotient are unchanged. -/
theorem lemma_B_4_12_two_of_stabilizers (hlocal : FifteenPointStabilizerInput.{u,w})
    {G : Type u} {V : Type w} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (v : V)
    (hspan : Submodule.span (ZMod 2) (Set.range fun g => ρ g v) = ⊤)
    (U : Submodule (ZMod 2) V) (hU : 1 < Module.finrank (ZMod 2) U)
    (hUorb : ∀ u ∈ U, u ≠ 0 → u ∈ Set.range (fun g => ρ g v))
    (hmodel : Nonempty (G ≃* PSL(4, ZMod 2)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 7)))
    (hodd : Odd (Nat.card (Set.range fun g => ρ g v)))
    (hquot : Nonempty (((vectorStabilizer ρ v) ⧸ pCore 2 (vectorStabilizer ρ v)) ≃*
      PSL(3, ZMod 2))) :
    Module.finrank (ZMod 2) V = 4 ∧
      Set.range (fun g => ρ g v) = {w : V | w ≠ 0} := by
  obtain ⟨htrans, hcard⟩ := hlocal ρ v hmodel hodd hquot
  exact finrank_eq_four_of_fifteen_point_orbit ρ v hspan U hU hUorb htrans hcard

end CFSG.Quasithin.ChapterB.SmallRecognition
