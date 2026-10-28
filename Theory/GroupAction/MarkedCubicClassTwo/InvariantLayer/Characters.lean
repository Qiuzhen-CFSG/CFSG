module

public import Theory.PGroup

/-!
# Common sign characters of commuting involutions

A nontrivial finite abelian three-group has a character onto a group of order
three, by taking any maximal-subgroup quotient. For an involution `a`, the two
characters `f ∘ a * f` and `f ∘ a / f` have signs plus and minus, respectively;
they cannot both vanish because the codomain has no involutions. Applying this
successively to two commuting involutions preserves the first sign. The kernel
of the resulting nonzero character is invariant and has index three.

This supplies the invariant subgroup in the central third layer in
Aschbacher–Smith F.6.16, printed p.308, combined manuscript of 1 March 2004.
No elementary-abelian hypothesis on the domain is required.
-/

public section

open Subgroup

namespace MarkedCubicClassTwo.InvariantLayer
variable {D C : Type*} [Group D] [CommGroup C]
private def signProject (f : D →* C) (a : MulAut D) (s : Bool) : D →* C :=
  if s then f.comp a.toMonoidHom * f else f.comp a.toMonoidHom / f

private theorem sign_character (a : MulAut D) (ha : a ^ 2 = 1)
    (hC : ∀ c : C, c ^ 2 = 1 → c = 1)
    (f : D →* C) (hf : f ≠ 1) :
    ∃ s : Bool, signProject f a s ≠ 1 ∧
      ∀ x, signProject f a s (a x) =
        if s then signProject f a s x else (signProject f a s x)⁻¹ := by
  have haa (x : D) : a (a x) = x := DFunLike.congr_fun ha x
  by_cases hp : signProject f a true = 1
  · refine ⟨false, ?_, ?_⟩
    · intro hm
      apply hf
      ext x
      have hp' : f (a x) * f x = 1 := DFunLike.congr_fun hp x
      have hm' : f (a x) / f x = 1 := DFunLike.congr_fun hm x
      have he : f (a x) = f x := div_eq_one.mp hm'
      exact hC (f x) (by simpa only [he, pow_two] using hp')
    · intro x
      change f (a (a x)) / f (a x) = (f (a x) / f x)⁻¹
      rw [haa]
      simp only [inv_div]
  · refine ⟨true, hp, ?_⟩
    intro x
    change f (a (a x)) * f (a x) = f (a x) * f x
    rw [haa, mul_comm]

private theorem signProject_preserves (a b : MulAut D) (hab : Commute a b)
    (f : D →* C) (s t : Bool)
    (hf : ∀ x, f (a x) = if s then f x else (f x)⁻¹) :
    ∀ x, signProject f b t (a x) =
      if s then signProject f b t x else (signProject f b t x)⁻¹ := by
  have hba (x : D) : b (a x) = a (b x) := (DFunLike.congr_fun hab.eq x).symm
  intro x
  cases s <;> cases t <;>
    simp only [signProject, Bool.false_eq_true, ↓reduceIte, MonoidHom.mul_apply,
      MonoidHom.div_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hba, hf,
      mul_inv_rev, inv_div]
  · simp only [div_eq_mul_inv, inv_inv, mul_comm]
  · exact mul_comm _ _

private theorem common_sign_character (a b : MulAut D)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b)
    (hC : ∀ c : C, c ^ 2 = 1 → c = 1)
    (f : D →* C) (hf : f ≠ 1) :
    ∃ g : D →* C, g ≠ 1 ∧
      (∀ x, g (a x) = 1 ↔ g x = 1) ∧
      (∀ x, g (b x) = 1 ↔ g x = 1) := by
  obtain ⟨s, hs, hsa⟩ := sign_character a ha hC f hf
  obtain ⟨t, ht, htb⟩ := sign_character b hb hC (signProject f a s) hs
  refine ⟨signProject (signProject f a s) b t, ht, ?_, ?_⟩
  · intro x
    rw [signProject_preserves a b hab _ s t hsa x]
    cases s <;> simp
  · intro x
    rw [htb]
    cases t <;> simp

/-- Two commuting involutions stabilize a subgroup of index three in a nontrivial
finite abelian three-group. -/
theorem exists_invariant_index_three {E : Type*} [CommGroup E] [Finite E] [Nontrivial E]
    (hE : IsPGroup 3 E) (a b : MulAut E)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : Commute a b) :
    ∃ U : Subgroup E, Nat.card (E ⧸ U) = 3 ∧
      (∀ x, a x ∈ U ↔ x ∈ U) ∧ (∀ x, b x ∈ U ↔ x ∈ U) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Fact (IsPGroup 3 E) := ⟨hE⟩
  obtain ⟨M, hM⟩ := IsCoatomic.exists_coatom (α := Subgroup E)
  have hc : Nat.card (E ⧸ M) = 3 := card_quotient_coatom_eq_prime hM
  have ht (c : E ⧸ M) (hh : c ^ 2 = 1) : c = 1 := by
    have h3 : c ^ 3 = 1 := by simpa only [hc] using (pow_card_eq_one' (x := c))
    simpa only [pow_succ, hh, one_mul] using h3
  have hq : QuotientGroup.mk' M ≠ 1 := by
    intro he
    apply hM.ne_top
    apply top_unique
    intro x _
    exact (QuotientGroup.eq_one_iff _).mp (DFunLike.congr_fun he x)
  obtain ⟨g, hg, hga, hgb⟩ := common_sign_character a b ha hb hab ht (QuotientGroup.mk' M) hq
  have hsurj : Function.Surjective g := by
    let : Fact (Nat.card (E ⧸ M)).Prime := ⟨hc ▸ Nat.prime_three⟩
    apply MonoidHom.range_eq_top.mp
    rcases eq_bot_or_eq_top_of_prime_card g.range with hr | hr
    · exfalso
      apply hg
      ext x
      exact mem_bot.mp (hr ▸ (show g x ∈ g.range from ⟨x, rfl⟩))
    · exact hr
  refine ⟨g.ker, ?_, hga, hgb⟩
  exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g hsurj).toEquiv).trans hc
end MarkedCubicClassTwo.InvariantLayer
