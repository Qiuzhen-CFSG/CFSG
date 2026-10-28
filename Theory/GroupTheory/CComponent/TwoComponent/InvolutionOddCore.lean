module

public import Theory.GroupTheory.CComponent.TwoComponent.Involution
public import Theory.GroupTheory.CyclicNormalCentralizer
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Odd-core criteria for the involutory B₂ property

A perfect subgroup centralizes every cyclic normal subgroup, because the
automorphism group of a cyclic group is abelian. Thus a two-component of a
finite group with cyclic odd core is an ordinary component. This permits an
odd torus in an involution centralizer; triviality of that torus is unnecessary.

When all involutory automorphisms of a simple group are inner, it suffices to
calculate odd cores of element centralizers. In the nonabelian case the group
is centerless, so the conjugating element itself has order two. The abelian
case is solvable and has no two-components.

Sources: GLS II, Definition 2.4 and Lemma 4.11
(`refs/KGroup/GLS2/ChapterA.tex`, `ChapterB.tex`). The model calculations that
discharge these criteria are separate from these elementary reductions.
-/

public section
open Subgroup Theory.GroupTheory

namespace Subgroup.IsTwoComponent
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

/-- A cyclic ambient odd core is centralized by every two-component. -/
theorem isComponent_of_isCyclic_oddCore (hL : L.IsTwoComponent)
    [IsCyclic (pPrimeCore 2 G)] : IsComponent G L := by
  let := hL.1.perfect
  apply hL.isComponent_of_centralizes_oddCore
  have hderived : L ≤ _root_.commutator G := by
    rw [← L.commutator_eq_self, commutator_def]
    exact commutator_mono le_top le_top
  exact hderived.trans (commutator_le_centralizer_of_isCyclic_normal _)

end Subgroup.IsTwoComponent

namespace Theory.GroupTheory.HasInvolutoryB2
variable {G : Type*} [Group G] [Finite G]

/-- Cyclic odd cores of the literal fixed subgroups suffice for B₂. -/
theorem of_fixed_cyclic_oddCore
    (h : ∀ (a : MulAut G), orderOf a = 2 →
      IsCyclic (pPrimeCore 2 a.fixedSubgroup)) : HasInvolutoryB2 G := by
  intro a ha L hL
  let := h a ha
  exact hL.isComponent_of_isCyclic_oddCore.2

/-- For simple groups with involutions inner, element centralizers suffice.
The conjugating element has order two; no Sylow-fixer hypothesis is used. -/
theorem of_inner_of_centralizer_cyclic_oddCore [IsSimpleGroup G]
    (hinner : ∀ (a : MulAut G), orderOf a = 2 → ∃ x : G, a = MulAut.conj x)
    (hcore : ∀ x : G, orderOf x = 2 →
      IsCyclic (pPrimeCore 2 (centralizer ({x} : Set G)))) : HasInvolutoryB2 G := by
  rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hz | hz
  · apply of_fixed_cyclic_oddCore
    intro a ha
    obtain ⟨x, hx, _, hf⟩ := MulAut.inner_involution_representative hz a ha (hinner a ha)
    rw [hf]
    exact hcore x hx
  · let : Group.IsSolvable G := Group.isSolvable_of_comm (fun x y =>
      (mem_center_iff.mp (show x ∈ center G from hz ▸ mem_top x) y).symm)
    exact of_solvable

/-- The trivial-odd-core specialization of the element-centralizer criterion. -/
theorem of_inner_of_centralizer_oddCore_eq_bot [IsSimpleGroup G]
    (hinner : ∀ (a : MulAut G), orderOf a = 2 → ∃ x : G, a = MulAut.conj x)
    (hcore : ∀ x : G, orderOf x = 2 →
      pPrimeCore 2 (centralizer ({x} : Set G)) = ⊥) : HasInvolutoryB2 G := by
  apply of_inner_of_centralizer_cyclic_oddCore hinner
  intro x hx
  rw [hcore x hx]
  infer_instance

end Theory.GroupTheory.HasInvolutoryB2
