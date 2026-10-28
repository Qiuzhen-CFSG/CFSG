module

public import Theory.SpecificGroups.PSL2.FieldResidualFixer.FixedSubgroup
public import Theory.SpecificGroups.PSL2.FieldResidualFixer.SmallField
public import Theory.SpecificGroups.PSL2.FieldCentralizerGeneration

/-!
# Full fixers of binary PSL₂ field residuals

For a nontrivial field involution, either its fixed field has an element other
than zero and one, or it is the two-element field. In the first case PSL₂ over
the fixed field is perfect, so its embedded two-residual is the whole fixed
subgroup; semilinear coverage and fixed-field Galois theory bound the full
fixer by two. In the second case the ambient field has four elements, and the
cubic-element calculation in `SmallField` excludes divisibility by four.

All fixers are taken in the full abstract automorphism group, and the residual
is the image of the fixed group's two-residual under its actual inclusion.
No abstract residual isomorphism is substituted for that inclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4(4) and the inspection in 16.4.9(1), printed pp.1171 and 1189.
-/

public section
open Subgroup Matrix BenderSuzuki.MatrixGroups BenderSuzuki.ZD.Linear
namespace Theory.PSL2.FieldResidualFixer
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
private theorem card_four_of_small_fixed (σ : F ≃+* F) (ho : orderOf σ = 2)
    (hsmall : ¬ ∃ x : FixedBy.subfield F σ, x ≠ 0 ∧ x ≠ 1) :
    Nat.card F = 4 := by
  have hcard : Nat.card (FixedBy.subfield F σ) = 2 := by
    apply (Nat.card_eq_two_iff' (1 : FixedBy.subfield F σ)).mpr
    refine ⟨0, zero_ne_one, ?_⟩
    intro y hy
    by_contra hne
    exact hsmall ⟨y, hne, hy⟩
  let H := Subgroup.zpowers σ
  let F₀ := FixedPoints.subfield H F
  let : Finite H := Finite.of_injective
    (fun g : H => (g.val : F → F)) (fun a b h => Subtype.ext (DFunLike.coe_injective h))
  let : Fintype H := Fintype.ofFinite H
  have hd : Module.finrank F₀ F = 2 := by
    rw [FixedPoints.finrank_eq_card, Fintype.card_eq_nat_card, Nat.card_zpowers, ho]
  have hFEq : F₀ = FixedBy.subfield F σ := by
    ext x
    change (∀ g : H, g • x = x) ↔ σ x = x
    constructor
    · intro hx; exact hx ⟨σ, Subgroup.mem_zpowers σ⟩
    · intro hx g; exact smul_eq_self_of_mem_zpowers g.property hx
  rw [Module.natCard_eq_pow_finrank (K := F₀), hd, hFEq, hcard]
  norm_num

private theorem residual_eq_fixed_of_large (σ : F ≃+* F)
    (hlarge : ∃ x : FixedBy.subfield F σ, x ≠ 0 ∧ x ≠ 1) :
    MulAut.embeddedFixedResidual 2 (BenderSuzuki.ZD.Linear.fieldAut σ) =
      (BenderSuzuki.ZD.Linear.fieldAut σ).fixedSubgroup := by
  have ha : BenderSuzuki.ZD.Linear.fieldAut σ = Theory.PSL2.fieldAut σ := by
    ext x
    obtain ⟨g, rfl⟩ := BenderSuzuki.Converse.pi_surjective x
    rw [BenderSuzuki.ZD.Linear.fieldAut_apply_pi]
    exact (Theory.PSL2.fieldAut_apply_quotientMap σ g).symm
  rw [ha, MulAut.embeddedFixedResidual, Theory.PSL2.fixed_twoResidual_eq_top σ hlarge,
    ← MonoidHom.range_eq_map, range_subtype]

/-- A nontrivial involutory coefficient automorphism has a residual fixer whose
order is not divisible by four, including the field-order-four endpoint. -/
theorem four_not_dvd_embeddedFixedResidual_fixer
    (σ : F ≃+* F) (hs : Function.Involutive σ) (hne : σ ≠ RingEquiv.refl F) :
    ¬ 4 ∣ Nat.card (fixingSubgroup (MulAut (PSL2MatrixGroup F))
      (MulAut.embeddedFixedResidual 2 (BenderSuzuki.ZD.Linear.fieldAut σ) :
        Set (PSL2MatrixGroup F))) := by
  have ho : orderOf σ = 2 := orderOf_eq_prime (by ext x; exact hs x) hne
  by_cases hlarge : ∃ x : FixedBy.subfield F σ, x ≠ 0 ∧ x ≠ 1
  · rw [residual_eq_fixed_of_large σ hlarge]
    have hbound := card_fixing_fixedSubgroup_le_two σ ho
    have hpos := Nat.card_pos (α := fixingSubgroup (MulAut (PSL2MatrixGroup F))
      ((BenderSuzuki.ZD.Linear.fieldAut σ).fixedSubgroup : Set (PSL2MatrixGroup F)))
    intro hdiv
    have hle := Nat.le_of_dvd hpos hdiv
    omega
  · exact four_not_dvd_fixer_of_card_four (card_four_of_small_fixed σ ho hlarge) σ

/-- The binary-degree formulation used by the Bender centralizer assembly. -/
theorem four_not_dvd_binary_embeddedFixedResidual_fixer {n : ℕ}
    (_hn : 2 ≤ n) (_hF : Nat.card F = 2 ^ n)
    (σ : F ≃+* F) (hs : Function.Involutive σ) (hne : σ ≠ RingEquiv.refl F) :
    ¬ 4 ∣ Nat.card (fixingSubgroup (MulAut (PSL2MatrixGroup F))
      (MulAut.embeddedFixedResidual 2 (BenderSuzuki.ZD.Linear.fieldAut σ) :
        Set (PSL2MatrixGroup F))) :=
  four_not_dvd_embeddedFixedResidual_fixer σ hs hne

end Theory.PSL2.FieldResidualFixer
