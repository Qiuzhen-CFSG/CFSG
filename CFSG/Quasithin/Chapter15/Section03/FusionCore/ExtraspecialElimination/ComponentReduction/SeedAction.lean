module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Actions

/-!
# The seed argument in the larger-field exclusion

An H-invariant subgroup fixing Z_S modulo Z fixes its entire H-conjugate
span modulo Z. Faithfulness of the specified section action then makes the
subgroup's star image trivial. This uses relative normalization of Z only.

The last theorem supplies the linear projection step on U_H/Z. Given the
B.2.14 decomposition into U_0/Z and fixed vectors, an inclusion of the Y_0
fixed space in the L fixed space on the first summand propagates to the
whole module and hence to the seed. The decomposition and the inclusion
are explicit inputs; the latter still requires the natural-module argument
for the actual larger-field model. These lemmas do not classify that model.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(k)–(l), printed p.1144.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction

variable {G : Type*} [Group G]

/-- An actor trivial on the literal section has trivial star image. -/
theorem starImage_eq_bot_of_commutator_le
    (H U Z A : Subgroup G) [IsElementaryAbelian 2 U]
    (action : SectionAction H U Z) (hAU : ⁅A, U⁆ ≤ Z) :
    starImage H A = ⊥ := by
  apply le_bot_iff.mp
  rintro x ⟨a, ha, rfl⟩
  change QuotientGroup.mk' (pCore 2 H) a = 1
  apply action.faithful
  ext w
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w.toMul
  have huw : Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u) = w :=
    congrArg Additive.ofMul hu
  rw [← huw, action.on_representatives]
  simp only [map_one, Module.End.one_apply]
  apply congrArg Additive.ofMul
  apply QuotientGroup.eq_iff_div_mem.mpr
  change ((a : G) * (u : G) * (a : G)⁻¹) / (u : G) ∈ Z
  simpa only [div_eq_mul_inv, commutatorElement_def] using
    hAU (commutator_mem_commutator (show (a : G) ∈ A from ha) u.property)

/-- Centralizing the seed modulo the layer suffices for an H-invariant subgroup. -/
theorem starImage_eq_bot_of_seed_commutator_le
    (H ZS Z L : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hZSH : ZS ≤ H) (hHL : H ≤ normalizer (L : Set G))
    (hseed : ⁅ZS, L⁆ ≤ Z) : starImage H L = ⊥ := by
  have hUC : localSpan ZS H ≤ commutatorPreimage H L Z := by
    apply conjugateSpanBy_le (le_commutatorPreimage hZSH hseed)
    exact commutatorPreimage_normalized H L Z H action.normalizes_layer
      H.le_normalizer hHL action.normalizes_layer
  apply starImage_eq_bot_of_commutator_le H (localSpan ZS H) Z L action
  rw [commutator_comm]
  exact (commutator_mono hUC le_rfl).trans
    (commutator_commutatorPreimage_le H L Z action.normalizes_layer)

open Representation.BinaryOffender

/-- The seed criterion stated in the actual section representation. -/
theorem starImage_eq_bot_of_fixed_seed
    (H ZS Z L : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hZSH : ZS ≤ H) (hLH : L ≤ H) (hHL : H ≤ normalizer (L : Set G))
    (hseed : ∀ z : ZS,
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H))
        ⟨(z : G), le_conjugateSpanBy ZS H z.property⟩) ∈
          fixedSpace action.representation (starImage H L)) :
    starImage H L = ⊥ := by
  apply starImage_eq_bot_of_seed_commutator_le H ZS Z L action hZSH hHL
  rw [commutator_comm]
  apply commutator_le.mpr
  intro l hl z hz
  let u : localSpan ZS H := ⟨z, le_conjugateSpanBy ZS H hz⟩
  let lH : H := ⟨l, hLH hl⟩
  have hf := hseed ⟨z, hz⟩
    ⟨QuotientGroup.mk' (pCore 2 H) lH, ⟨lH, hl, rfl⟩⟩
  change action.representation (QuotientGroup.mk' (pCore 2 H) lH)
    (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H)) u)) =
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H)) u) at hf
  rw [action.on_representatives] at hf
  have he := congrArg Additive.toMul hf
  have hc := QuotientGroup.eq_iff_div_mem.mp he
  change (l * z * l⁻¹) / z ∈ Z at hc
  simpa only [div_eq_mul_inv, commutatorElement_def] using hc

private theorem fixedSpace_le_of_projection
    {K W : Type*} [Group K] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) K W) (A B : Subgroup K) (D : Submodule (ZMod 2) W)
    (hsplit : D ⊔ fixedSpace ρ ⊤ = ⊤)
    (hpart : D ⊓ fixedSpace ρ A ≤ fixedSpace ρ B) :
    fixedSpace ρ A ≤ fixedSpace ρ B := by
  intro v hv
  obtain ⟨d, hd, c, hc, rfl⟩ := Submodule.mem_sup.mp (hsplit ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) W)))
  have hcA : c ∈ fixedSpace ρ A := fun a => hc ⟨a, trivial⟩
  have hdA : d ∈ fixedSpace ρ A := by
    have hh := (fixedSpace ρ A).sub_mem hv hcA
    simpa only [add_sub_cancel_right] using hh
  exact (fixedSpace ρ B).add_mem (hpart ⟨hd, hdA⟩) (fun b => hc ⟨b, trivial⟩)

/-- Apply the seed criterion after splitting off the global fixed space. -/
theorem starImage_eq_bot_of_fixedSpace_projection
    (H ZS Z L Y0 : Subgroup G) [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (hZSH : ZS ≤ H) (hLH : L ≤ H) (hHL : H ≤ normalizer (L : Set G))
    (D : Submodule (ZMod 2) (Additive (localSpan ZS H ⧸ Z.subgroupOf (localSpan ZS H))))
    (hsplit : D ⊔ fixedSpace action.representation ⊤ = ⊤)
    (hpart : D ⊓ fixedSpace action.representation (starImage H Y0) ≤
      fixedSpace action.representation (starImage H L))
    (hseed : ∀ z : ZS,
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (localSpan ZS H))
        ⟨(z : G), le_conjugateSpanBy ZS H z.property⟩) ∈
          fixedSpace action.representation (starImage H Y0)) :
    starImage H L = ⊥ := by
  apply starImage_eq_bot_of_fixed_seed H ZS Z L action hZSH hLH hHL
  intro z
  exact fixedSpace_le_of_projection action.representation _ _ D hsplit hpart (hseed z)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction
