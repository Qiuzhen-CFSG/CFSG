module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryImages
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.BinaryRelators
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary

/-!
# Odd Held-cover centers from relations in the actual double cover

The established binary-relator calculation supplies a surjective lift of the
seven-relator presentation into any finite perfect central double cover.
The two marked-word contracts then imply injectivity by the local image
bound. Prime-kernel reduction gives odd center for every finite quasisimple
group with the literal central quotient `Held.He`.

The two word contracts remain explicit: this is a conditional assembly,
not the unconditional Held multiplier theorem. Their independent producers
must supply the even equations and the odd equations under those even inputs.

Sources: Aschbacher--Smith I.1.1 and I.1.3, p.407; John Bray's ATLAS
`Held/Model/Source/HeG1-P1.M`. The binary normalization uses the proved
`binaryRelatorLifting`, without multiplier assumptions.
-/

public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
open PerfectCentralCovering Theory.GroupTheory
universe u

/-- Binary normalization lifts the original presentation onto an actual
perfect central double cover, preserving the marked map to Held. -/
theorem exists_presentation_lift {E : Type u} [Group E] [Finite E]
    (f : Cover E He) (hcard : Nat.card f.toMonoidHom.ker = 2) :
    ∃ h : Presentation →* E,
      Function.Surjective h ∧ f.toMonoidHom.comp h = presentationMap := by
  let := f.isPerfect
  obtain ⟨z, _, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : f.toMonoidHom.ker)).mp hcard
  have hzsq : (z : E) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := z)
    rw [hcard] at hh
    exact congrArg Subtype.val hh
  obtain ⟨x₀, hx⟩ := f.surjective a
  obtain ⟨y₀, hy⟩ := f.surjective b
  have hres (i : Fin 7) :
      relationWord x₀ y₀ i = 1 ∨ relationWord x₀ y₀ i = (z : E) := by
    have hk : relationWord x₀ y₀ i ∈ f.toMonoidHom.ker := by
      rw [MonoidHom.mem_ker, map_relationWord, hx, hy]
      exact relations i
    by_cases hone : relationWord x₀ y₀ i = 1
    · exact Or.inl hone
    · exact Or.inr (congrArg Subtype.val (hzuniq ⟨_, hk⟩
        (fun he => hone (congrArg Subtype.val he))))
  obtain ⟨ε, η, hrel⟩ := binaryRelatorLifting E z x₀ y₀
    (f.ker_le_center z.property) hzsq hres
  let gen : Fin 2 → E := ![x₀ * z.val ^ ε.val, y₀ * z.val ^ η.val]
  have hr (r : FreeGroup (Fin 2)) (hr : r ∈ definingRelators) :
      FreeGroup.lift gen r = 1 := by
    obtain ⟨i, rfl⟩ := hr
    rw [map_relationWord]
    simpa only [FreeGroup.lift_apply_of, gen, Matrix.cons_val_zero,
      Matrix.cons_val_one] using hrel i
  let h : Presentation →* E := PresentedGroup.toGroup hr
  have htriangle : f.toMonoidHom.comp h = presentationMap := by
    apply PresentedGroup.ext
    intro i
    rw [MonoidHom.comp_apply, presentationMap_of]
    change f.toMonoidHom (h (PresentedGroup.of i)) = generator i
    rw [show h (PresentedGroup.of i) = gen i from PresentedGroup.toGroup.of hr]
    fin_cases i
    · change f.toMonoidHom (x₀ * z.val ^ ε.val) = a
      rw [map_mul, map_pow, z.property, one_pow, mul_one, hx]
    · change f.toMonoidHom (y₀ * z.val ^ η.val) = b
      rw [map_mul, map_pow, z.property, one_pow, mul_one, hy]
  exact ⟨h,
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect f.toMonoidHom h
      (htriangle.symm ▸ presentationMap_surjective) f.ker_le_center,
    htriangle⟩

/-- The two word producers exclude every finite perfect central double cover.
Both producers are still required. -/
theorem no_double_cover_of_binary_m1
    (heven : BinaryEvenRelations.{u}) (hodd : BinaryOddRelations.{u})
    {E : Type u} [Group E] [Finite E] (f : Cover E He) :
    Nat.card f.toMonoidHom.ker ≠ 2 := by
  intro hcard
  obtain ⟨h, hsurj, ht⟩ := exists_presentation_lift f hcard
  have he := heven E f hcard h ht
  have ho := hodd E f hcard h ht he
  have hi := map_injective_of_imageRelations h hsurj f.toMonoidHom ht
    (imageRelations_of_even_odd h he ho)
  rw [(MonoidHom.ker_eq_bot_iff _).mpr hi, Subgroup.card_bot] at hcard
  exact (by decide : (1 : ℕ) ≠ 2) hcard

/-- The exact cover-center conclusion, conditional only on the two marked
word families. This does not discharge those families. -/
theorem odd_center_of_binary_m1
    (heven : BinaryEvenRelations.{u}) (hodd : BinaryOddRelations.{u})
    {X : Type u} [Group X] [Finite X] [IsQuasisimple X]
    (e : (X ⧸ Subgroup.center X) ≃* He) : Odd (Nat.card (Subgroup.center X)) :=
  odd_center_of_no_double_cover
    (fun _ _ _ f => no_double_cover_of_binary_m1 heven hodd f) e

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction
