module

public import Theory.Alternating.Aut
public import Theory.GroupTheory.HomFromFactorization
public import Theory.GroupTheory.SpecificGroups.FiveFour

/-!
# A symmetric extension from a marked alternating action

An injective copy of A_n and an involution inducing conjugation by a
specified odd involution t construct an injective copy of S_n. The map
retains both the alternating embedding and the original involution.
Compatible maps descend from the elementary semidirect factorization;
faithfulness follows because S_n acts faithfully on A_n for n at least four.
No classification of automorphisms of A_n is used.

This supplies the actual extension in the alternating-row inspection of
Aschbacher--Smith, Proposition 2.2.2, printed pp.519--520, together with
Lemma 1.1.5(3)(c),(d), printed pp.501--502 (1 March 2004 manuscript).
-/

public section
open Subgroup Equiv Equiv.Perm

namespace Theory.GroupTheory.MarkedAlternatingExtension

private theorem cyclic_two_cases (b : FiveFour.Cyclic 2) :
    b = 1 ∨ b = FiveFour.generator 2 := by
  exact (by decide +kernel : ∀ b : FiveFour.Cyclic 2,
    b = 1 ∨ b = FiveFour.generator 2) b

theorem alternating_sup_odd_involution {n : ℕ} (t : Perm (Fin n))
    (ht : t.sign = -1) : alternatingGroup (Fin n) ⊔ zpowers t = ⊤ := by
  apply top_unique
  intro s _
  rcases Int.units_eq_one_or s.sign with hs | hs
  · exact mem_sup_left hs
  · have he : t⁻¹ * s ∈ alternatingGroup (Fin n) := by
      change (t⁻¹ * s).sign = 1
      rw [map_mul, map_inv, ht, hs]
      norm_num
    have hm := (alternatingGroup (Fin n) ⊔ zpowers t).mul_mem
      (mem_sup_right (mem_zpowers t)) (mem_sup_left he)
    simpa only [mul_inv_cancel_left] using hm

/-- The given odd involution action constructs the literal symmetric extension.
Only injectivity of the alternating subgroup and its marked action are used. -/
theorem exists_embedding {G : Type*} [Group G] {n : ℕ} (hn : 4 ≤ n)
    (j : alternatingGroup (Fin n) →* G) (hj : Function.Injective j)
    (t : Perm (Fin n)) (ht : t.sign = -1) (ht2 : t ^ 2 = 1)
    (z : G) (hz2 : z ^ 2 = 1)
    (haction : ∀ a : alternatingGroup (Fin n),
      j (MulAut.conjNormal t a) = z * j a * z⁻¹) :
    ∃ F : Perm (Fin n) →* G, Function.Injective F ∧
      (∀ a : alternatingGroup (Fin n), F a = j a) ∧ F t = z ∧
      F.range = j.range ⊔ zpowers z := by
  let A := alternatingGroup (Fin n)
  let i := FiveFour.cyclicHom t ht2
  let f := FiveFour.cyclicHom z hz2
  let φ : FiveFour.Cyclic 2 →* MulAut A := MulAut.conjNormal.comp i
  have hi (b : FiveFour.Cyclic 2) (a : A) :
      (φ b a : Perm (Fin n)) = i b * a * (i b)⁻¹ := rfl
  have hf (b : FiveFour.Cyclic 2) (a : A) :
      j (φ b a) = f b * j a * (f b)⁻¹ := by
    rcases cyclic_two_cases b with rfl | rfl
    · simp [φ, i, f]
    · simpa only [φ, MonoidHom.comp_apply, i, f, FiveFour.cyclicHom_generator]
        using haction a
  have hoverlap (b : FiveFour.Cyclic 2) (a : A)
      (he : i b = (a : Perm (Fin n))) : f b = j a := by
    rcases cyclic_two_cases b with rfl | rfl
    · have ha : a = 1 := Subtype.ext (by simpa only [map_one, Subgroup.coe_one] using he.symm)
      simp only [ha, map_one]
    · have he' : t = (a : Perm (Fin n)) := by
        simpa only [i, FiveFour.cyclicHom_generator] using he
      have hs : (a : Perm (Fin n)).sign = 1 := a.property
      rw [← he', ht] at hs
      norm_num at hs
  have hfactor (s : Perm (Fin n)) : ∃ b : FiveFour.Cyclic 2,
      ∃ a : A, i b * a = s := by
    rcases Int.units_eq_one_or s.sign with hs | hs
    · exact ⟨1, ⟨s, hs⟩, by simp only [map_one, one_mul]⟩
    · have he : t⁻¹ * s ∈ A := by
        change (t⁻¹ * s).sign = 1
        rw [map_mul, map_inv, ht, hs]
        norm_num
      refine ⟨FiveFour.generator 2, ⟨t⁻¹ * s, he⟩, ?_⟩
      simp only [i, FiveFour.cyclicHom_generator, mul_inv_cancel_left]
  obtain ⟨F, hFi, hFj⟩ := exists_hom_of_factorization φ i A.subtype f j hi hf
    hoverlap hfactor
  have hFt : F t = z := by
    simpa only [i, f, FiveFour.cyclicHom_generator] using hFi (FiveFour.generator 2)
  have hFinj : Function.Injective F := by
    apply (MonoidHom.ker_eq_bot_iff F).mp
    apply bot_unique
    intro s hs
    have hs1 : F s = 1 := hs
    have hconj : (MulAut.conjNormal (H := A) s : MulAut A) = 1 := by
      apply MulEquiv.ext
      intro a
      apply hj
      rw [← hFj, ← hFj]
      change F (s * (a : Perm (Fin n)) * s⁻¹) = F a
      simp only [map_mul, map_inv, hs1, one_mul, inv_one, mul_one]
    exact GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n hn
      (hconj.trans (map_one MulAut.conjNormal).symm)
  have hFrange : F.range = j.range ⊔ zpowers z := by
    have hFA : A.map F = j.range := by
      ext x
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, (hFj ⟨a, ha⟩).symm⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a, a.property, hFj a⟩
    rw [MonoidHom.range_eq_map]
    rw [← alternating_sup_odd_involution t ht, Subgroup.map_sup, hFA,
      MonoidHom.map_zpowers, hFt]
  exact ⟨F, hFinj, hFj, hFt, hFrange⟩

end Theory.GroupTheory.MarkedAlternatingExtension
