module

public import CFSG.Quasithin.ChapterI.Section06To08.Basic
public import Theory.GroupTheory.TwoLocalUniqueness

/-!
# The uniqueness criterion for TI-subgroups

Lemma I.6.1(2) follows from uniqueness among maximal two-local overgroups.
For a nonidentity element of the given 2-subgroup, the normalizer of its
cyclic subgroup is two-local and contains its centralizer. Thus the general
uniqueness argument applies without an elementary-abelian assumption.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma I.6.1(2), printed p. 424.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterI.Section06To08

variable {G : Type*} [Group G] [Finite G]

/-- I.6.1(2): the normalizer of a 2-subgroup being the unique maximal two-local
overgroup of a subgroup centralizing it implies the TI property. -/
theorem lemma_I_6_1_2 (X M L : Subgroup G) (hX : IsPGroup 2 X)
    (hM : M = Subgroup.normalizer (X : Set G))
    (hmax : IsMaximalTwoLocal M) (_hLM : L ≤ M)
    (hunique : ∀ P : Subgroup G, IsMaximalTwoLocal P → L ≤ P → P = M)
    (hLX : L ≤ Subgroup.centralizer (X : Set G)) : IsTISubgroup X := by
  intro g hg z hz
  have hgM : g ∉ M := by simpa only [hM] using hg
  have hinter : X ⊓ X.map (MulAut.conj g).toMonoidHom = ⊥ := by
    apply Theory.GroupTheory.inf_conjugate_eq_bot_of_unique_maximal
      (F := {P | IsTwoLocal P}) (H := L)
      (fun e _ hP => Theory.GroupTheory.isTwoLocal_map_aut hP e)
      hmax hunique
      (Theory.GroupTheory.normalizer_eq_of_isMaximalTwoLocal hmax).le hLX ?_ hgM
    intro x hx hx1
    let A := Subgroup.zpowers x
    have hAX : A ≤ X := Subgroup.zpowers_le.mpr hx
    have hpA : IsPGroup 2 A :=
      hX.of_injective (Subgroup.inclusion hAX) (Subgroup.inclusion_injective hAX)
    have hA : A ≠ ⊥ := by
      intro hbot
      exact hx1 (Subgroup.zpowers_eq_bot.mp hbot)
    refine ⟨Subgroup.normalizer (A : Set G), ⟨A, hA, hpA, rfl⟩, ?_⟩
    rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hz' : z ∈ X ⊓ X.map (MulAut.conj g).toMonoidHom := by
    refine ⟨hz.1, ?_⟩
    obtain ⟨x, hx, heq⟩ := hz.2
    exact ⟨x, hx, heq⟩
  simpa only [hinter, Subgroup.mem_bot, Set.mem_singleton_iff] using hz'

end CFSG.Quasithin.ChapterI.Section06To08
