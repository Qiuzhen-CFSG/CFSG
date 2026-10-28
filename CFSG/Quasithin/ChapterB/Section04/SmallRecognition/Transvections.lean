module

public import Theory.Representation.BinaryTransvectionGroups.OrbitClosure

/-!+# B.4.10: the action of the normal closure of a full transvection group

The lower-layer orbit-closure theorem extends linear forms off the orbit span
and conjugates the original root group. This application retains the faithful
source action, its original nonzero center, and normal closure inside G.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma B.4.10, printed p.96.
-/

public section

namespace CFSG.Quasithin.ChapterB.SmallRecognition
open BinaryLinear BinaryTransvectionGroups

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- B.4.10: Aut_L(U) is GL(U), with U the actual orbit span and L the
normal closure in the original acting group of the full root group. -/
theorem lemma_B_4_10 (ρ : G →* GL V) (_hfaith : Function.Injective ρ)
    (u : V) (_hu : u ≠ 0) (hfull : radical (centerLine u) ≤ ρ.range) :
    (rootNormalClosure ρ u).map (orbitSpanAction ρ u) = ⊤ :=
  rootNormalClosure_action_eq_top ρ u hfull

/-- Every specified automorphism of the orbit span is induced by an element
of the original normal closure; this gives the literal action equality. -/
theorem transvection_normalClosure_realizes (ρ : G →* GL V)
    (u : V) (hfull : radical (centerLine u) ≤ ρ.range)
    (a : GL (orbitSpan ρ u)) :
    ∃ g ∈ rootNormalClosure ρ u, ∀ w : orbitSpan ρ u, ρ g w = (a w : V) := by
  have ha : a ∈ (rootNormalClosure ρ u).map (orbitSpanAction ρ u) :=
    rootNormalClosure_action_eq_top ρ u hfull ▸ Subgroup.mem_top a
  obtain ⟨g, hg, he⟩ := ha
  exact ⟨g, hg, fun w => congrArg (fun b : GL (orbitSpan ρ u) => (b w : V)) he⟩

end CFSG.Quasithin.ChapterB.SmallRecognition
