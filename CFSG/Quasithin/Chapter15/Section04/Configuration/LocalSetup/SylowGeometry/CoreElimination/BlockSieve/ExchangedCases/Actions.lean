module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.Setup

/-!
# Compatible local and internal conjugation actions

The inclusion of the local orbit into the internal H-module induces an
injective binary linear map. Conjugation intertwines on actual representatives.
For the component quotient, this descends along the two actual component
embeddings. A map from the whole local core quotient to H/O₂(H) is unnecessary
and is not asserted: its existence would require a separate core-containment
proof.

These maps extend `Input.local_module_comparison` for the module sieve in
Aschbacher–Smith, combined manuscript (1 March 2004), C.2.7 and C.1.34,
and the proof of 15.4.20, printed p.1164.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases
variable {D H : Type*} [Group D] [Group H]

/-- A homomorphism that maps the actual local module into the internal module. -/
noncomputable def moduleMap (f : D →* H) (V : Subgroup D) (W : Subgroup H)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W] (hVW : V.map f ≤ W) :
    Additive V →ₗ[ZMod 2] Additive W :=
  ((f.comp V.subtype).codRestrict W (fun v => hVW (mem_map_of_mem f v.property))).toAdditive.toZModLinearMap 2

theorem moduleMap_injective (f : D →* H) (hf : Function.Injective f)
    (V : Subgroup D) (W : Subgroup H)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W] (hVW : V.map f ≤ W) :
    Function.Injective (moduleMap f V W hVW) := by
  intro v w hvw
  apply Additive.toMul.injective
  apply Subtype.ext
  apply hf
  exact congrArg (fun x : Additive W => (x.toMul : H)) hvw

/-- Intertwining is valid on representatives, with no assumed map D/O₂(D) → H/O₂(H). -/
theorem moduleMap_equivariant (f : D →* H) (V : Subgroup D) (W : Subgroup H)
    [V.Normal] [W.Normal] [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (hVW : V.map f ≤ W)
    (hV : centralizer (V : Set D) = pCore 2 D)
    (hW : centralizer (W : Set H) = pCore 2 H) (g : D) (v : Additive V) :
    moduleMap f V W hVW (coreAction V hV (QuotientGroup.mk' _ g) v) =
      coreAction W hW (QuotientGroup.mk' _ (f g)) (moduleMap f V W hVW v) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change f (((coreAction V hV (QuotientGroup.mk' _ g) v).toMul : D)) = _
  rw [coreAction_apply, coreAction_apply, map_mul, map_mul, map_inv]
  rfl

/-- A subnormal subgroup's core quotient embeds through the actual inclusion. -/
noncomputable def subnormalCoreMap [Finite H] (B : Subgroup H) (hB : B.IsSubnormal) :
    (B ⧸ pCore 2 B) →* (H ⧸ pCore 2 H) :=
  QuotientGroup.map _ _ B.subtype (pCore_subnormal_eq_comap 2 hB).le

theorem subnormalCoreMap_injective [Finite H] (B : Subgroup H) (hB : B.IsSubnormal) :
    Function.Injective (subnormalCoreMap B hB) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [subnormalCoreMap, QuotientGroup.ker_map, ← pCore_subnormal_eq_comap 2 hB,
    QuotientGroup.map_mk'_self]

theorem subnormalCoreMap_apply [Finite H] (B : Subgroup H) (hB : B.IsSubnormal) (g : B) :
    subnormalCoreMap B hB (QuotientGroup.mk' _ g) = QuotientGroup.mk' _ (g : H) := rfl

/-- The local-to-internal module map respects a component's quotient action
whenever its two actual quotient embeddings agree on representatives. -/
theorem moduleMap_component_equivariant
    {B : Type*} [Group B] (f : D →* H) (b : B →* D)
    (V : Subgroup D) (W : Subgroup H)
    [V.Normal] [W.Normal] [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (hVW : V.map f ≤ W)
    (hV : centralizer (V : Set D) = pCore 2 D)
    (hW : centralizer (W : Set H) = pCore 2 H)
    (bD : (B ⧸ pCore 2 B) →* (D ⧸ pCore 2 D))
    (bH : (B ⧸ pCore 2 B) →* (H ⧸ pCore 2 H))
    (hbD : ∀ g, bD (QuotientGroup.mk' _ g) = QuotientGroup.mk' _ (b g))
    (hbH : ∀ g, bH (QuotientGroup.mk' _ g) = QuotientGroup.mk' _ (f (b g)))
    (g : B ⧸ pCore 2 B) (v : Additive V) :
    moduleMap f V W hVW (coreAction V hV (bD g) v) =
      coreAction W hW (bH g) (moduleMap f V W hVW v) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
  rw [hbD, hbH]
  exact moduleMap_equivariant f V W hVW hV hW (b g) v

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases
