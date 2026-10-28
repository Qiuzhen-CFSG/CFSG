module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.LocalControl

/-!
# Initial reductions for contrary involution fusion

Permutation of the two nontrivial factors puts the whole Sylow subgroup in H.
A nonidentity factor element has its centralizer in H by the defining
transporter generators. An outside transporter into S must therefore send
its element to one which exchanges the two factors.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, paragraph beginning “Assume a is an involution”.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

theorem LocalControl.sylow_le_generated (l : LocalControl S A₁ A₂)
    (h : Hypotheses S A₁ A₂) : (S : Subgroup G) ≤ intersectionGenerated A₁ A₂ := by
  intro s hs
  obtain ⟨a, hane⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.left_ne_bot
  have hane' : (a : G) ≠ 1 := fun he => hane (Subtype.ext he)
  apply transporter_mem_intersectionGenerated (Or.inl a.property) hane'
  have hm : s⁻¹ * (a : G) * s ∈ conjugate A₁ s := mem_map.mpr ⟨a, a.property, by simp⟩
  rcases l.permutes_pair s hs with hh | hh
  · exact Or.inl (by rwa [hh.1] at hm)
  · exact Or.inr (by rwa [hh.1] at hm)

omit [Finite G] in
theorem Hypotheses.centralizer_le_generated (_h : Hypotheses S A₁ A₂)
    {a : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha1 : a ≠ 1) :
    centralizer ({a} : Set G) ≤ intersectionGenerated A₁ A₂ := by
  intro x hx
  apply transporter_mem_intersectionGenerated ha ha1
  have he := mem_centralizer_singleton_iff.mp hx
  simpa only [mul_assoc, ← he, inv_mul_cancel_left] using ha

theorem LocalControl.swap_of_outside_transporter (l : LocalControl S A₁ A₂)
    (h : Hypotheses S A₁ A₂) {a g : G}
    (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha1 : a ≠ 1)
    (hg : g ∉ intersectionGenerated A₁ A₂) (ht : g⁻¹ * a * g ∈ S) :
    conjugate A₁ (g⁻¹ * a * g) = A₂ ∧ conjugate A₂ (g⁻¹ * a * g) = A₁ := by
  rcases l.permutes_pair _ ht with hn | hs
  · exact (hg (h.transporter_mem_of_left_normalizer ha ha1
      ⟨ht, (mem_normalizer_iff_conjugate_eq _ _).mpr hn.1⟩)).elim
  · exact hs

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
