module

public import Theory.GroupTheory.CComponent.TwoComponent
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# The simple-group B₂ condition

The condition here concerns involutory automorphisms of the given group. For
a simple group this is exactly GLS II, Definition 2.4. The sectionwise property
of an arbitrary group, which tests every simple section, is a separate notion.

An actual group isomorphism transports the automorphism, its order, its fixed
subgroup and the two-component. Solvable fixed groups have no C-components;
otherwise it suffices that the two-component centralize the ambient odd core.
These reductions support the known-simple input to GLS II, Lemma 5.28.
-/

@[expose] public section

open Subgroup

namespace Theory.GroupTheory

/-- The B₂ condition on involutory automorphisms, without a simplicity guard. -/
def HasInvolutoryB2 (G : Type*) [Group G] : Prop :=
  ∀ (a : MulAut G), orderOf a = 2 →
    ∀ L : Subgroup a.fixedSubgroup, L.IsTwoComponent → IsQuasisimple L

namespace HasInvolutoryB2

variable {G H : Type*} [Group G] [Group H]

/-- Transport uses the induced equivalence of the actual fixed subgroups. -/
theorem of_mulEquiv (hH : HasInvolutoryB2 H) (e : G ≃* H) : HasInvolutoryB2 G := by
  intro a ha L hL
  let f := MulAut.fixedSubgroupCongr e a
  have hq : IsQuasisimple (L.map f.toMonoidHom) :=
    hH (MulAut.congr e a) (((MulAut.congr e).orderOf_eq a).trans ha)
    (L.map f.toMonoidHom) (hL.map_equiv f)
  exact IsQuasisimple.of_mulEquiv (f.subgroupMap L).symm (hG := hq)

theorem mulEquiv_iff (e : G ≃* H) : HasInvolutoryB2 G ↔ HasInvolutoryB2 H :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

/-- A solvable fixed subgroup cannot contain a two-component. -/
theorem of_fixed_solvable
    (h : ∀ a : MulAut G, orderOf a = 2 → Group.IsSolvable a.fixedSubgroup) :
    HasInvolutoryB2 G := by
  intro a ha L hL
  let := h a ha
  exact (hL.1.not_isSolvable inferInstance).elim

/-- In particular the condition holds in every solvable group. -/
theorem of_solvable [Group.IsSolvable G] : HasInvolutoryB2 G :=
  of_fixed_solvable fun _ _ => inferInstance

/-- A trivial odd core in each involution fixed subgroup suffices. -/
theorem of_fixed_oddCore_eq_bot [Finite G]
    (h : ∀ a : MulAut G, orderOf a = 2 → pPrimeCore 2 a.fixedSubgroup = ⊥) :
    HasInvolutoryB2 G := by
  intro a ha L hL
  exact (hL.isComponent_of_oddCore_eq_bot (h a ha)).2

/-- Only centralization of the fixed subgroup's odd core is needed. -/
theorem of_fixed_centralizes_oddCore [Finite G]
    (h : ∀ (a : MulAut G), orderOf a = 2 →
      ∀ L : Subgroup a.fixedSubgroup, L.IsTwoComponent →
        L ≤ centralizer (pPrimeCore 2 a.fixedSubgroup : Set a.fixedSubgroup)) :
    HasInvolutoryB2 G := by
  intro a ha L hL
  exact (hL.isComponent_of_centralizes_oddCore (h a ha L hL)).2

end HasInvolutoryB2
end Theory.GroupTheory
