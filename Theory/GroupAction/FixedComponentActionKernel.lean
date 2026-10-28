module
public import Theory.GroupAction.CommutingFixedComponentFixer
/-!
# The centralizer kernel of a two-element component action

The normalizer action has kernel equal to the literal ambient centralizer. A marked involution in its image and the two-element pointwise-fixer bound force that kernel to have index two.

Source: Aschbacher–Smith 2.5.19, printed pp.560–563.
-/

public section
open Subgroup Theory.GroupTheory
namespace MulAut
variable {G : Type*} [Group G] [Finite G]

/-- An involution in a two-element pointwise actor group gives the literal
centralizer kernel index two. -/
theorem fixed_component_action_kernel_index_two
    (X R : Subgroup G) (hRN : R ≤ normalizer (X : Set G))
    (t : G) (htR : t ∈ R)
    (a : MulAut X) (ha : orderOf a = 2)
    (hact : ∀ x : X, (a x : G) = t * (x : G) * t⁻¹)
    (B : Subgroup a.fixedSubgroup)
    (hRt : R ≤ centralizer ({t} : Set G))
    (hRB : ∀ r ∈ R, ∀ x : B,
      r * (((x : a.fixedSubgroup) : X) : G) = (((x : a.fixedSubgroup) : X) : G) * r)
    (hcard : Nat.card (commutingFixedComponentFixer a B) ≤ 2) :
    ((R ⊓ centralizer (X : Set G)).subgroupOf R).index = 2 := by
  let f : R →* MulAut X := X.normalizerMonoidHom.comp (inclusion hRN)
  have hf (r : R) (x : X) : (f r x : G) = (r : G) * (x : G) * (r : G)⁻¹ := rfl
  have hfa : f ⟨t,htR⟩ = a := by
    apply MulEquiv.ext
    intro x
    exact Subtype.ext ((hf ⟨t,htR⟩ x).trans (hact x).symm)
  have hfrange : f.range ≤ commutingFixedComponentFixer a B := by
    rintro _ ⟨r, rfl⟩
    constructor
    · apply mem_centralizer_singleton_iff.mpr
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      change ((f r) (a x) : G) = (a ((f r) x) : G)
      rw [hf, hact, hact, hf]
      have hrt : (r : G) * t = t * (r : G) :=
        mem_centralizer_singleton_iff.mp (hRt r.property)
      calc
        _ = ((r : G) * t) * (x : G) * ((r : G) * t)⁻¹ := by group
        _ = (t * (r : G)) * (x : G) * (t * (r : G))⁻¹ := by rw [hrt]
        _ = _ := by group
    · rintro ⟨x, ⟨y, hy, rfl⟩⟩
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hRB r r.property ⟨y,hy⟩)
  have hupper : Nat.card f.range ≤ 2 := (card_le_of_le hfrange).trans hcard
  have hlower : 2 ≤ Nat.card f.range := by
    let aR : f.range := ⟨a, ⟨⟨t,htR⟩,hfa⟩⟩
    have ho : orderOf aR = 2 := (orderOf_injective f.range.subtype f.range.subtype_injective aR).symm.trans ha
    have hd : 2 ∣ Nat.card f.range := ho ▸ orderOf_dvd_natCard aR
    exact Nat.le_of_dvd (Nat.card_pos (α := f.range)) hd
  have hker : f.ker = (R ⊓ centralizer (X : Set G)).subgroupOf R := by
    ext r
    constructor
    · intro hr
      refine ⟨r.property, ?_⟩
      intro x hx
      have he := DFunLike.congr_fun hr (⟨x,hx⟩ : X)
      have he' := congrArg Subtype.val he
      exact (mul_inv_eq_iff_eq_mul.mp he').symm
    · intro hr
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hr.2 x x.property).symm
  rw [← hker, index_ker]
  omega
end MulAut
