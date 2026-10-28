module

public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.Reduction
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.Contracts
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.GroupTheory.Covering

/-!
# Two-primary reductions for central covers of Held

An even central kernel in a finite perfect group produces a perfect central
cover with kernel of order two. For the concrete Held model, a double cover
can in turn be eliminated from two independent presentation inputs: the
canonical presentation map is injective, and the seven relators admit binary
central lifting. The lifted presentation map is surjective by perfectness of
the covering group; its triangle over the faithful presentation then forces
the covering itself to be injective.

The source corollary is odd order of `center X` when the actual quotient
`X / center X` is isomorphic to `Held.He`. This file proves only the stated
conditional reductions. It does not yet establish either presentation input,
and hence does not yet prove the unconditional Held multiplier corollary.

Source: Aschbacher–Smith, I.1.1 and I.1.3, printed p.407; GLS3 Table 5.3p.
The explicit words come from John Bray's ATLAS `HeG1-P1`. That source file's
informal presentation identification invokes triviality of the multiplier,
so it cannot be reused as a proof of the missing injectivity here.
-/

namespace Held.CentralCovers.TwoPrimary
open PerfectCentralCovering Theory.GroupTheory
universe u

private theorem lift_from_relators {E : Type u} [Group E]
    (x y : E) (hrel : ∀ i : Fin 7, relationWord x y i = 1) :
    ∃ h : Presentation →* E, h (PresentedGroup.of 0) = x ∧
      h (PresentedGroup.of 1) = y := by
  let gen : Fin 2 → E := ![x, y]
  have hr (r : FreeGroup (Fin 2)) (hr : r ∈ definingRelators) :
      FreeGroup.lift gen r = 1 := by
    obtain ⟨i, rfl⟩ := hr
    rw [map_relationWord]
    simpa only [FreeGroup.lift_apply_of, gen, Matrix.cons_val_zero,
      Matrix.cons_val_one] using hrel i
  exact ⟨PresentedGroup.toGroup hr, PresentedGroup.toGroup.of hr,
    PresentedGroup.toGroup.of hr⟩

/-- A faithful presentation and the explicit binary relator calculation exclude
perfect central double covers of the concrete model. Both premises remain
separate mathematical obligations. -/
public theorem no_double_cover_of_presentation
    (hfaithful : Function.Injective presentationMap)
    (hlift : BinaryRelatorLifting.{u})
    {E : Type u} [Group E] [Finite E] (f : Cover E He) :
    Nat.card f.toMonoidHom.ker ≠ 2 := by
  intro hcard
  let := f.isPerfect
  obtain ⟨z, _, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : f.toMonoidHom.ker)).mp hcard
  have hzsq : (z : E) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := z)
    rw [hcard] at hh
    exact congrArg Subtype.val hh
  obtain ⟨x, hx⟩ := f.surjective a
  obtain ⟨y, hy⟩ := f.surjective b
  have hres (i : Fin 7) : relationWord x y i = 1 ∨ relationWord x y i = (z : E) := by
    have hk : relationWord x y i ∈ f.toMonoidHom.ker := by
      rw [MonoidHom.mem_ker, map_relationWord, hx, hy]
      exact relations i
    by_cases hone : relationWord x y i = 1
    · exact Or.inl hone
    · exact Or.inr (congrArg Subtype.val (hzuniq ⟨_, hk⟩
        (fun he => hone (congrArg Subtype.val he))))
  obtain ⟨ε, η, hrel⟩ := hlift E z x y (f.ker_le_center z.property) hzsq hres
  obtain ⟨h, hzero, hone⟩ := lift_from_relators _ _ hrel
  have htriangle : f.toMonoidHom.comp h = presentationMap := by
    apply PresentedGroup.ext
    intro i
    rw [MonoidHom.comp_apply, presentationMap_of]
    fin_cases i
    · change f.toMonoidHom (h (PresentedGroup.of 0)) = generator 0
      rw [hzero, map_mul, map_pow, z.property, one_pow, mul_one, hx]
      rfl
    · change f.toMonoidHom (h (PresentedGroup.of 1)) = generator 1
      rw [hone, map_mul, map_pow, z.property, one_pow, mul_one, hy]
      rfl
  have hsurj : Function.Surjective h :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect f.toMonoidHom h
      (htriangle.symm ▸ presentationMap_surjective) f.ker_le_center
  have hf : Function.Injective f.toMonoidHom := by
    intro e₁ e₂ he
    obtain ⟨p₁, rfl⟩ := hsurj e₁
    obtain ⟨p₂, rfl⟩ := hsurj e₂
    apply congrArg h
    apply hfaithful
    change (f.toMonoidHom.comp h) p₁ = (f.toMonoidHom.comp h) p₂ at he
    rwa [htriangle] at he
  have hk := (MonoidHom.ker_eq_bot_iff f.toMonoidHom).mpr hf
  rw [hk, Subgroup.card_bot] at hcard
  exact (by decide : (1 : ℕ) ≠ 2) hcard

private def coverOfCenterQuotient {X : Type u} [Group X] [IsQuasisimple X]
    (e : (X ⧸ Subgroup.center X) ≃* He) : Cover X He where
  toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
  isPerfect := inferInstance
  ker_le_center := by
    intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply e.injective
    exact hx.trans (map_one e).symm

private theorem coverOfCenterQuotient_ker {X : Type u} [Group X] [IsQuasisimple X]
    (e : (X ⧸ Subgroup.center X) ≃* He) :
    (coverOfCenterQuotient e).toMonoidHom.ker = Subgroup.center X := by
  apply le_antisymm (coverOfCenterQuotient e).ker_le_center
  intro x hx
  change e (QuotientGroup.mk' (Subgroup.center X) x) = 1
  rw [show QuotientGroup.mk' (Subgroup.center X) x = 1 from
    (QuotientGroup.eq_one_iff x).mpr hx, map_one]

/-- The exact arbitrary-universe center conclusion follows from exclusion of
perfect central double covers. The quotient map has kernel exactly the center;
no independent simplicity or perfectness certification of Held is required. -/
public theorem odd_center_of_no_double_cover
    (hno : ∀ (Y : Type u) [Group Y] [Finite Y] (g : Cover Y He),
      Nat.card g.toMonoidHom.ker ≠ 2)
    {X : Type u} [Group X] [Finite X] [IsQuasisimple X]
    (e : (X ⧸ Subgroup.center X) ≃* He) : Odd (Nat.card (Subgroup.center X)) := by
  have h := PrimaryReduction.odd_card_kernel_of_no_double_cover (coverOfCenterQuotient e) hno
  rwa [coverOfCenterQuotient_ker] at h

/-- Conditional presentation route to odd centers of quasisimple Held covers.
This is not the unconditional source theorem: presentation faithfulness and
binary relator lifting must still be proved and supplied. -/
public theorem odd_center_of_presentation
    (hfaithful : Function.Injective presentationMap)
    (hlift : BinaryRelatorLifting.{u})
    {X : Type u} [Group X] [Finite X] [IsQuasisimple X]
    (e : (X ⧸ Subgroup.center X) ≃* He) : Odd (Nat.card (Subgroup.center X)) :=
  odd_center_of_no_double_cover
    (fun _ _ _ f => no_double_cover_of_presentation hfaithful hlift f) e

end Held.CentralCovers.TwoPrimary
