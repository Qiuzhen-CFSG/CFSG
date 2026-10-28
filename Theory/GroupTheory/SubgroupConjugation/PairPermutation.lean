module
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Permuting a pair of conjugate subgroups

If the orbit of A lies in {A,B}, and an element of H carries A to B, the
whole H-action either fixes both entries or exchanges them. Injectivity of
conjugation deals also with coincident entries. The same original conjugator
is retained, with left-conjugation convention.

Source application: Aschbacher--Smith, 14.6.22(1), printed p.1038.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- The actual two-element orbit gives a simultaneous permutation of both entries. -/
theorem pair_permutation_of_conjugate_orbit
    (H A B : Subgroup G)
    (hp : ∀ x ∈ H, A.map (MulAut.conj x).toMonoidHom = A ∨
      A.map (MulAut.conj x).toMonoidHom = B)
    (s : G) (hs : s ∈ H) (he : A.map (MulAut.conj s).toMonoidHom = B) :
    ∀ x ∈ H,
      (A.map (MulAut.conj x).toMonoidHom = A ∧ B.map (MulAut.conj x).toMonoidHom = B) ∨
      (A.map (MulAut.conj x).toMonoidHom = B ∧ B.map (MulAut.conj x).toMonoidHom = A) := by
  intro x hx
  have hb : B.map (MulAut.conj x).toMonoidHom = A ∨
      B.map (MulAut.conj x).toMonoidHom = B := by
    have hh := hp (x*s) (H.mul_mem hx hs)
    have hc : (MulAut.conj x).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
        (MulAut.conj (x*s)).toMonoidHom := by ext a; simp [MulAut.conj_apply,mul_assoc]
    have hm : B.map (MulAut.conj x).toMonoidHom = A.map (MulAut.conj (x*s)).toMonoidHom := by
      rw [←he,map_map,hc]
    simpa only [hm] using hh
  rcases hp x hx with ha | ha <;> rcases hb with hb | hb
  · have hAB : A = B := map_injective (MulAut.conj x).injective (ha.trans hb.symm)
    exact Or.inl ⟨ha,hb.trans hAB⟩
  · exact Or.inl ⟨ha,hb⟩
  · exact Or.inr ⟨ha,hb⟩
  · have hAB : A = B := map_injective (MulAut.conj x).injective (ha.trans hb.symm)
    exact Or.inr ⟨ha,hb.trans hAB.symm⟩
end Subgroup
