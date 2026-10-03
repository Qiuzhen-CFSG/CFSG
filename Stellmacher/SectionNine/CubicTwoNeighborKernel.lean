module
public import Stellmacher.SectionNine.CubicLocalAction

/-!
# Two fixed neighbors detect the cubic local kernel

In a supplied cubic local action, an element of the middle-vertex stabilizer
fixing two distinct neighbors belongs to the middle vertex core. No global
Section Nine hypotheses or critical path are needed beyond the degree-three
and kernel data in `CubicLocalActionConclusion`.

A third neighbor completes the three-element neighborhood. Its image must
be one of those neighbors; injectivity excludes the first two because they
are already fixed. Thus every neighbor is fixed, and the supplied kernel
characterization applies. This shared criterion supplies both the actor
closure and the central core-intersection arguments in Stellmacher (9.4).

Source: the cubic local action consequences of (9.3), used in (9.4), printed
pp.50–52 of `refs/files/stellmacher-n-group.pdf`. The proof is extracted
unchanged from the reviewed actor-closure module.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem cubic_mem_core_of_fix_two_neighbors
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (middle left right : Γ.Vertex)
    (hlocal : CubicLocalActionConclusion Γ middle)
    (hleft : Γ.adjacent middle left) (hright : Γ.adjacent middle right)
    (hne : left ≠ right) (actor : GAt Γ middle)
    (hfixleft : Γ.act (actor : G) left = left)
    (hfixright : Γ.act (actor : G) right = right) : (actor : G) ∈ QAt Γ middle := by
  apply (hlocal.kernel actor).2
  intro neighbor hneighbor
  by_cases hsame : neighbor = left
  · simpa only [hsame] using hfixleft
  by_cases hsameright : neighbor = right
  · simpa only [hsameright] using hfixright
  classical
  let Points := {vertex // Γ.adjacent middle vertex}
  let : Finite Γ.Vertex := Γ.finiteVertex
  let := Fintype.ofFinite Points
  have hcover : ({⟨left, hleft⟩, ⟨right, hright⟩, ⟨neighbor, hneighbor⟩} :
      Finset Points) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← Nat.card_eq_fintype_card, hlocal.degree]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · intro heq
      exact hsameright (congrArg Subtype.val (Finset.mem_singleton.mp heq)).symm
    · intro hmem
      rcases Finset.mem_insert.mp hmem with heq | heq
      · exact hne (congrArg Subtype.val heq)
      · exact hsame (congrArg Subtype.val (Finset.mem_singleton.mp heq)).symm
  have hfixmiddle := (Set.ext_iff.mp (Γ.stabilizer_def middle) actor).mp actor.property
  have hacted : Γ.adjacent middle (Γ.act (actor : G) neighbor) := by
    have htransport := adjacent_act Γ (actor : G) hneighbor
    rwa [hfixmiddle] at htransport
  have hmem : (⟨Γ.act (actor : G) neighbor, hacted⟩ : Points) ∈
      ({⟨left, hleft⟩, ⟨right, hright⟩, ⟨neighbor, hneighbor⟩} : Finset Points) := by
    rw [hcover]; exact Finset.mem_univ _
  have hinj : Function.Injective (Γ.act (actor : G)) := by
    intro first second heq
    have hinv := congrArg (Γ.act (actor : G)⁻¹) heq
    simpa only [← Γ.act_mul, mul_inv_cancel, Γ.act_one] using hinv
  simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff] at hmem
  rcases hmem with heq | heq | heq
  · exact (hsame (hinj (heq.trans hfixleft.symm))).elim
  · exact (hsameright (hinj (heq.trans hfixright.symm))).elim
  · exact heq

end Stellmacher.SectionNine
