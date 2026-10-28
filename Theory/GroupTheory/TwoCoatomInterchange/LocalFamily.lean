module
public import Theory.GroupTheory.TwoCoatomInterchange

/-!
# Two maximal overgroups inside an invariant local family

The two-parabolic argument needs coverage only for the actual invariant
intersection and automorphic images of the two parabolics. A property
preserved by those automorphisms therefore suffices. The application uses
characteristic two, for which symplectic fixed-space geometry supplies
coverage, without asserting coverage for arbitrary proper overgroups.

Source: Aschbacher--Smith 2.5.2(2), printed p.551.
-/

public section
namespace Subgroup
variable {D : Type*} [Group D]

/-- The two-coatom geometry turns nontrivial action into actual interchange
and identifies the invariant proper intersection with B. -/
theorem eq_inf_and_exists_interchange_of_two_coatoms_in_family
    (B P Q I : Subgroup D) (hP : IsCoatom P) (hQ : IsCoatom Q)
    (hPQ : P ≠ Q) (hB : P ⊓ Q = B)
    (C : Subgroup D → Prop)
    (hCP : C P) (hCQ : C Q) (hCI : C I)
    (hcover : ∀ J : Subgroup D, B ≤ J → C J → J ≠ ⊤ → J ≤ P ∨ J ≤ Q)
    (A : Set (MulAut D))
    (hCA : ∀ a ∈ A, ∀ J, C J → C (J.map a.toMonoidHom))
    (hAB : ∀ a ∈ A, B.map a.toMonoidHom = B)
    (hAI : ∀ a ∈ A, I.map a.toMonoidHom = I)
    (hnon : ¬ ∀ a ∈ A, P.map a.toMonoidHom = P ∧ Q.map a.toMonoidHom = Q)
    (hBI : B ≤ I) (hI : I ≠ ⊤) :
    I = B ∧ ∃ a ∈ A, P.map a.toMonoidHom = Q ∧ Q.map a.toMonoidHom = P := by
  classical
  have hperm (a : MulAut D) (ha : a ∈ A) (J : Subgroup D)
      (hc : IsCoatom J) (hb : B ≤ J) (hCJ : C J) :
      J.map a.toMonoidHom = P ∨ J.map a.toMonoidHom = Q := by
    have hm : IsCoatom (J.map a.toMonoidHom) := (a.mapSubgroup.isCoatom_iff J).mpr hc
    have hle : B ≤ J.map a.toMonoidHom := (hAB a ha).symm ▸ map_mono hb
    rcases hcover _ hle (hCA a ha J hCJ) hm.ne_top with hp | hq
    · exact Or.inl ((hm.le_iff_eq hP.ne_top).mp hp).symm
    · exact Or.inr ((hm.le_iff_eq hQ.ne_top).mp hq).symm
  have hex : ∃ a ∈ A, P.map a.toMonoidHom = Q ∧ Q.map a.toMonoidHom = P := by
    by_contra hn
    apply hnon
    intro a ha
    have hneq : P.map a.toMonoidHom ≠ Q.map a.toMonoidHom :=
      fun he => hPQ (Subgroup.map_injective a.injective he)
    rcases hperm a ha P hP (hB ▸ inf_le_left) hCP with hp | hp <;>
      rcases hperm a ha Q hQ (hB ▸ inf_le_right) hCQ with hq | hq
    · exact (hneq (hp.trans hq.symm)).elim
    · exact ⟨hp, hq⟩
    · exact (hn ⟨a, ha, hp, hq⟩).elim
    · exact (hneq (hp.trans hq.symm)).elim
  obtain ⟨a, ha, hp, hq⟩ := hex
  refine ⟨le_antisymm ?_ hBI, a, ha, hp, hq⟩
  rw [← hB]
  rcases hcover I hBI hCI hI with hi | hi
  · have hj := map_mono (f := a.toMonoidHom) hi
    rw [hAI a ha, hp] at hj
    exact le_inf hi hj
  · have hj := map_mono (f := a.toMonoidHom) hi
    rw [hAI a ha, hq] at hj
    exact le_inf hj hi

end Subgroup
