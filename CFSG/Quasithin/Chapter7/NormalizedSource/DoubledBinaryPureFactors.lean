module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureLine

/-!
# Preserving the two factors at the original pure line

An operator fixing a nonzero vector in either marked factor cannot induce
a graph automorphism, since graph operators exchange the factors. Its inner
implementation preserves both factors. Every seed-moving normalizer element
has the same dual factor as its conjugate seed; equal orders turn the
coordinate containment into equality. Thus an offender's original conjugator
can be retained when a new choice of natural–dual coordinates is used.

NonFFSourceDoubledBinaryPureCore applies these results to the local Sylow
subgroup at the actual commutator line, retaining both original factors.
Source: Aschbacher–Smith H.4.1 and 7.6.1, printed pp.380,702,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureFactors
open BinaryLinearThree NaturalDual ChapterE
variable {G : Type*} [_root_.Group G]

/-- A nonzero pure fixed vector rules out graph action, so the literal
point centralizer preserves both original factors. -/
theorem pureLine_normalizes_factors
    (W₀ A B Z : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hAW : A ≤ W₀) (hBW : B ≤ W₀)
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (a : Automizer W₀ ≃* MulAut Group)
    (hcov : ∀ b g w, E (automizerRepresentation W₀ b (E.symm (action g (E w)))) =
      action (a b g) (E (automizerRepresentation W₀ b w)))
    (hA : ∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ A)
    (hB : ∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ B)
    (hZ : Z ≠ ⊥) (hpure : Z ≤ A ∨ Z ≤ B) :
    normalizer (W₀ : Set G) ⊓ centralizer (Z : Set G) ≤
      normalizer (A : Set G) ⊓ normalizer (B : Set G) := by
  have acts (n : (normalizer (W₀ : Set G) ⊓ centralizer (Z : Set G) : Subgroup G)) :
      ∃ g : Group, ∀ w : Additive W₀,
        E (automizerRepresentation W₀
          (W₀.normalizerMonoidHom.rangeRestrict ⟨n,n.property.1⟩) w) = action g (E w) := by
    let b : Automizer W₀ := W₀.normalizerMonoidHom.rangeRestrict ⟨n,n.property.1⟩
    let c := E.symm.trans ((LinearMap.GeneralLinearGroup.toLinearEquiv
      ((automizerRepresentation W₀).asGroupHom b)).trans E)
    have hc (g : Group) (x : Space) : c (action g x) = action (a b g) (c x) := by
      change E (automizerRepresentation W₀ b (E.symm (action g x))) =
        action (a b g) (E (automizerRepresentation W₀ b (E.symm x)))
      simpa only [E.apply_symm_apply] using hcov b g (E.symm x)
    have hi : a b ∈ MulAut.innerSubgroup Group := by
      by_contra ho
      obtain ⟨z,hz,hzb⟩ := SetLike.not_le_iff_exists.mp (show ¬ Z ≤ ⊥ from
        fun hh => hZ (le_bot_iff.mp hh))
      have hz1 : z ≠ 1 := fun he => hzb (he ▸ (⊥ : Subgroup G).one_mem)
      have hzW : z ∈ W₀ := hpure.elim (fun h => hAW (h hz)) (fun h => hBW (h hz))
      let w : Additive W₀ := Additive.ofMul ⟨z,hzW⟩
      have hw : c (E w) = E w := by
        change E (automizerRepresentation W₀ b (E.symm (E w))) = E w
        rw [E.symm_apply_apply]
        congr 1
        apply Additive.toMul.injective
        apply Subtype.ext
        change (n : G) * z * (n : G)⁻¹ = z
        rw [← n.property.2 z hz,mul_inv_cancel_right]
      have hn : E w ≠ 0 := by
        intro he
        have hh := E.map_eq_zero_iff.mp he
        exact hz1 (congrArg (fun x : Additive W₀ => (x.toMul : G)) hh)
      rcases hpure with hZA | hZB
      · have he : (E w).2 = 0 := (hA w).mpr (hZA hz)
        have hh := (outer_swaps (a b) c hc ho).1 (E w).1
        rw [show ((E w).1,0) = E w from Prod.ext rfl he.symm,hw] at hh
        exact hn (Prod.ext hh he)
      · have he : (E w).1 = 0 := (hB w).mpr (hZB hz)
        have hh := (outer_swaps (a b) c hc ho).2 (E w).2
        rw [show (0,(E w).2) = E w from Prod.ext he.symm rfl,hw] at hh
        exact hn (Prod.ext he hh)
    obtain ⟨g,hg⟩ := inner_operator (a b) c hc hi
    refine ⟨g,fun w => ?_⟩
    have hh := LinearEquiv.congr_fun hg (E w)
    change E (automizerRepresentation W₀ b (E.symm (E w))) = action g (E w) at hh
    simpa only [E.symm_apply_apply] using hh
  have step (n : (normalizer (W₀ : Set G) ⊓ centralizer (Z : Set G) : Subgroup G))
      (x : G) (hx : x ∈ W₀) :
      (x ∈ A → (n : G) * x * (n : G)⁻¹ ∈ A) ∧
      (x ∈ B → (n : G) * x * (n : G)⁻¹ ∈ B) := by
    obtain ⟨g,hg⟩ := acts n
    let w : Additive W₀ := Additive.ofMul ⟨x,hx⟩
    let y := automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict ⟨n,n.property.1⟩) w
    constructor
    · intro hxA
      change (y.toMul : G) ∈ A
      apply (hA y).mp
      change (E (automizerRepresentation W₀ _ w)).2 = 0
      rw [hg]
      change W.dual g (E w).2 = 0
      rw [(hA w).mpr hxA,map_zero]
    · intro hxB
      change (y.toMul : G) ∈ B
      apply (hB y).mp
      change (E (automizerRepresentation W₀ _ w)).1 = 0
      rw [hg]
      change W g (E w).1 = 0
      rw [(hB w).mpr hxB,map_zero]
  apply le_inf
  · apply le_normalizer_iff.mpr
    intro n hn x hx
    exact (step ⟨n,hn⟩ x (hAW hx)).1 hx
  · apply le_normalizer_iff.mpr
    intro n hn x hx
    exact (step ⟨n,hn⟩ x (hBW hx)).2 hx


/-- The marked natural factor has its actual order eight. -/
theorem natural_factor_card [Finite G]
    (W₀ A : Subgroup G) [IsElementaryAbelian 2 W₀] (hAW : A ≤ W₀)
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (hA : ∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ A) : Nat.card A = 8 := by
  let f : Vector → A := fun v => ⟨(E.symm (v,0)).toMul,
    (hA _).mp (by rw [E.apply_symm_apply])⟩
  have hi : Function.Injective f := by
    intro v u he
    have hh : E.symm (v,0) = E.symm (u,0) := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact congrArg (fun x : A => (x : G)) he
    exact congrArg Prod.fst (E.symm.injective hh)
  have hs : Function.Surjective f := by
    intro v
    let w : Additive W₀ := Additive.ofMul ⟨v,hAW v.property⟩
    refine ⟨(E w).1,?_⟩
    apply Subtype.ext
    have hh : ((E w).1,0) = E w := Prod.ext rfl ((hA w).mpr v.property).symm
    change ((E.symm ((E w).1,0)).toMul : G) = v
    rw [hh,E.symm_apply_apply]
    rfl
  have hc := Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)
  rw [← hc]
  change Nat.card (Fin 3 → ZMod 2) = 8
  rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  rfl

/-- Every outer conjugate of the marked natural factor is the same dual
factor. This permits keeping the original offender's conjugator. -/
theorem outer_conjugate_eq [Finite G]
    (W₀ A B : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hAW : A ≤ W₀) (hcard : Nat.card A = Nat.card B)
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (a : Automizer W₀ ≃* MulAut Group)
    (hcov : ∀ b g w, E (automizerRepresentation W₀ b (E.symm (action g (E w)))) =
      action (a b g) (E (automizerRepresentation W₀ b w)))
    (hA : ∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ A)
    (hB : ∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ B)
    (n : normalizer (W₀ : Set G))
    (hn : a (W₀.normalizerMonoidHom.rangeRestrict n) ∉ MulAut.innerSubgroup Group) :
    A.map (MulAut.conj (n : G)).toMonoidHom = B := by
  apply eq_of_le_of_card_ge
  · let b := W₀.normalizerMonoidHom.rangeRestrict n
    let c := E.symm.trans ((LinearMap.GeneralLinearGroup.toLinearEquiv
      ((automizerRepresentation W₀).asGroupHom b)).trans E)
    have hc (g : Group) (x : Space) : c (action g x) = action (a b g) (c x) := by
      change E (automizerRepresentation W₀ b (E.symm (action g x))) =
        action (a b g) (E (automizerRepresentation W₀ b (E.symm x)))
      simpa only [E.apply_symm_apply] using hcov b g (E.symm x)
    rintro _ ⟨v,hv,rfl⟩
    let w : Additive W₀ := Additive.ofMul ⟨v,hAW hv⟩
    let y := automizerRepresentation W₀ b w
    change (y.toMul : G) ∈ B
    apply (hB y).mp
    have hh := (outer_swaps (a b) c hc hn).1 (E w).1
    have hz : ((E w).1,0) = E w := Prod.ext rfl ((hA w).mpr hv).symm
    rw [hz] at hh
    change (E (automizerRepresentation W₀ b (E.symm (E w)))).1 = 0 at hh
    simpa only [E.symm_apply_apply] using hh
  · rw [card_map_of_injective (MulAut.conj (n : G)).injective,hcard]

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureFactors
