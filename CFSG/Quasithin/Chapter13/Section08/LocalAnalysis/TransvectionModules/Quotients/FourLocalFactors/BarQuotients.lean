module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.BarQuotients.OriginalGeneration
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.BarQuotients.StabilizerQuotients

/-!
# The original barred local groups in 13.8.6(4)

For the original natural module of Aschbacher–Smith, Notations 13.2.1 and
13.3.3, we identify the images of the two relative normalizer residuals with
natural line and plane stabilizers. Their quotients by their intrinsic two-cores
are S₃. The bar is the action modulo C_LT(V). Its supplied S₆ marking is compared
with the original natural coordinates through an explicit automorphism; it need
not preserve the two natural parabolic classes.

The proof supplements each relative residual by the actual Sylow subgroup T,
then uses the concrete duad and syntheme core calculations. The index-two flag
subgroup V₃ is a hyperplane in the original V, and its conjugates under L₂ span
V. This gives the original-module generation used in the proof of 13.8.6(4),
without assuming any of the actions on U_H/V or U₂/V asserted there.

Source: *The Classification of Quasithin Groups*, Notations 13.2.1 and 13.3.3,
the original natural-module flags on pp. 915–916, and 13.8.6(4), p. 948.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.BarQuotients
open ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
variable {G : Type*} [Group G] [Finite G] {L T V V₁ : Subgroup G}

/-- The change from the supplied bar marking to the original natural action. -/
noncomputable def coordinateTwist (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (e : (barMap (L ⊔ T) V n.normalizes_V).range ≃* Equiv.Perm (Fin 6)) :
    MulAut (Equiv.Perm (Fin 6)) := e.symm.trans (naturalBarEquiv n hfixed e)

omit [Finite G] in
theorem coordinateTwist_apply (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (e : (barMap (L ⊔ T) V n.normalizes_V).range ≃* Equiv.Perm (Fin 6))
    (g : (L ⊔ T : Subgroup G)) :
    coordinateTwist n hfixed e (e ((barMap (L ⊔ T) V n.normalizes_V).rangeRestrict g)) =
      n.permutation g := by
  simp only [coordinateTwist, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    naturalBarEquiv_apply]

theorem sourceResidual_eq_local (n : NaturalSetup L T V V₁) (X : Subgroup G) :
    sourceResidual L T X = (pResidual 2 (L ⊓ normalizer (X : Set G) : Subgroup G)).map
      (L ⊓ normalizer (X : Set G)).subtype := by
  have hT := n.sylow.isPGroup'.map (L ⊔ T).subtype
  rw [n.sylow_eq, map_subgroupOf_eq_of_le (show T ≤ L ⊔ T from le_sup_right)] at hT
  exact FiveSeed.BarMarking.normalizer_residual_eq L X T hT n.normalizes_L

theorem sourceResidual_le_L (n : NaturalSetup L T V V₁) (X : Subgroup G) :
    sourceResidual L T X ≤ L := by
  rw [sourceResidual_eq_local n X]
  exact (map_subtype_le _).trans inf_le_left

noncomputable def localStabilizerEquiv (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (e : (barMap (L ⊔ T) V n.normalizes_V).range ≃* Equiv.Perm (Fin 6))
    (X Li : Subgroup G) (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hX : X = sourceLinePreimage n.naturalMap W)
    (hTX : T ≤ normalizer (X : Set G)) (hLi : Li = sourceResidual L T X) :
    localBar n Li ≃* subspaceStabilizer (BinaryPermutation.naturalRepresentation (Fin 6)) W :=
  ((naturalBarEquiv n hfixed e).subgroupMap (localBar n Li)).trans
    (MulEquiv.subgroupCongr (localBar_map n hfixed e X Li W hX hTX hLi))

noncomputable def localQuotient (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (e : (barMap (L ⊔ T) V n.normalizes_V).range ≃* Equiv.Perm (Fin 6))
    (X Li : Subgroup G) (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hd : Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 2)
    (hX : X = sourceLinePreimage n.naturalMap W)
    (hTX : T ≤ normalizer (X : Set G)) (hLi : Li = sourceResidual L T X) :
    (localBar n Li ⧸ pCore 2 (localBar n Li)) ≃* Equiv.Perm (Fin 3) := by
  let c := localStabilizerEquiv n hfixed e X Li W hX hTX hLi
  exact (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
    (stabilizer_quotient n.permutation.range n.alternating_le_range (imageSylow n) W hd
      (imageSylow_stable n X W hX hTX)).some

/-- The constructed local S₃ action has the intrinsic local two-core as its
kernel. This core is inside the barred local group, not an ambient core. -/
theorem localQuotient_kernel (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (e : (barMap (L ⊔ T) V n.normalizes_V).range ≃* Equiv.Perm (Fin 6))
    (X Li : Subgroup G) (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hd : Module.finrank (ZMod 2) W = 1 ∨ Module.finrank (ZMod 2) W = 2)
    (hX : X = sourceLinePreimage n.naturalMap W)
    (hTX : T ≤ normalizer (X : Set G)) (hLi : Li = sourceResidual L T X) :
    ((localQuotient n hfixed e X Li W hd hX hTX hLi).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 (localBar n Li)))).ker = pCore 2 (localBar n Li) := by
  let q := localQuotient n hfixed e X Li W hd hX hTX hLi
  ext x
  change q (QuotientGroup.mk' (pCore 2 (localBar n Li)) x) = 1 ↔ _
  rw [← q.map_one, q.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

/-- The first source local group, barred by C_LT(V), has intrinsic two-core
quotient S₃. -/
noncomputable def firstQuotient (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (e : (barMap (L ⊔ T) V n.normalizes_V).range ≃* Equiv.Perm (Fin 6))
    (L₁ : Subgroup G) (hL₁ : L₁ = sourceResidual L T V₁) :
    (localBar n L₁ ⧸ pCore 2 (localBar n L₁)) ≃* Equiv.Perm (Fin 3) :=
  localQuotient n hfixed e V₁ L₁ n.point (Or.inl n.point_dim) n.line_eq n.line_stable hL₁

/-- The second source local group has intrinsic two-core quotient S₃, using
the actual original coordinate plane. -/
noncomputable def secondQuotient (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (e : (barMap (L ⊔ T) V n.normalizes_V).range ≃* Equiv.Perm (Fin 6))
    (V₂ L₂ : Subgroup G) (W₂ : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hd : Module.finrank (ZMod 2) W₂ = 2)
    (hV₂ : V₂ = sourceLinePreimage n.naturalMap W₂)
    (hT₂ : T ≤ normalizer (V₂ : Set G)) (hL₂ : L₂ = sourceResidual L T V₂) :
    (localBar n L₂ ⧸ pCore 2 (localBar n L₂)) ≃* Equiv.Perm (Fin 3) :=
  localQuotient n hfixed e V₂ L₂ W₂ (Or.inr hd) hV₂ hT₂ hL₂

/-- Both actual barred local quotients and original-module generation from
the source coordinate plane and flag index. -/
theorem source_quotients_and_generation (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (e : (barMap (L ⊔ T) V n.normalizes_V).range ≃* Equiv.Perm (Fin 6))
    (V₂ V₃ L₁ L₂ : Subgroup G) (W₂ : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hd : Module.finrank (ZMod 2) W₂ = 2)
    (hV₂ : V₂ = sourceLinePreimage n.naturalMap W₂)
    (hT₂ : T ≤ normalizer (V₂ : Set G))
    (h3V : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hL₁ : L₁ = sourceResidual L T V₁) (hL₂ : L₂ = sourceResidual L T V₂) :
    Nonempty ((localBar n L₁ ⧸ pCore 2 (localBar n L₁)) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((localBar n L₂ ⧸ pCore 2 (localBar n L₂)) ≃* Equiv.Perm (Fin 3)) ∧
      V = conjugateSpanBy V₃ L₂ :=
  ⟨⟨firstQuotient n hfixed e L₁ hL₁⟩,
    ⟨secondQuotient n hfixed e V₂ L₂ W₂ hd hV₂ hT₂ hL₂⟩,
    original_generation n hfixed V₂ V₃ L₂ W₂ hd hV₂ hT₂ h3V hindex hL₂⟩

/-- Cardinality and containment suffice to construct the original coordinate
plane; no relation to the distinct U_H/V₁ coordinates is required. -/
theorem source_quotients_and_generation_of_card (n : NaturalSetup L T V V₁)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (e : (barMap (L ⊔ T) V n.normalizes_V).range ≃* Equiv.Perm (Fin 6))
    (V₂ V₃ L₁ L₂ : Subgroup G) (h23 : V₂ ≤ V₃) (h3V : V₃ ≤ V)
    (hcard₂ : Nat.card V₂ = 4) (hT₂ : T ≤ normalizer (V₂ : Set G))
    (hindex : V₃.relIndex V = 2)
    (hL₁ : L₁ = sourceResidual L T V₁) (hL₂ : L₂ = sourceResidual L T V₂) :
    Nonempty ((localBar n L₁ ⧸ pCore 2 (localBar n L₁)) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((localBar n L₂ ⧸ pCore 2 (localBar n L₂)) ≃* Equiv.Perm (Fin 3)) ∧
      V = conjugateSpanBy V₃ L₂ :=
  source_quotients_and_generation n hfixed e V₂ V₃ L₁ L₂ (naturalImage n V₂)
    (naturalImage_plane n hfixed V₂ (h23.trans h3V) hcard₂)
    (naturalImage_preimage n hfixed V₂ (h23.trans h3V)).symm
    hT₂ h3V hindex hL₁ hL₂

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.BarQuotients

end
