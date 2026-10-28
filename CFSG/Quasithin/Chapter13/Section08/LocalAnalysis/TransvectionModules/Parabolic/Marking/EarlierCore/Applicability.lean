module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.Generation
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Basic

/-!
# Applicability of the ordinary natural-module hypotheses

The coordinates are on V itself. They identify its centralizer in L with
O₂(L), show that C_V(L) is trivial, and compute the orders of the actual
flag subgroups from their dimensions. These are representation and flag
facts, independent of the ambient local conclusions of 13.5.4.

Source: Aschbacher–Smith, Notation 13.2.1, p.877, Notation 13.3.3, p.885,
and Remark 13.5.3 preceding Lemma 13.5.4, p.916.
-/

@[expose] public section
open Subgroup Module BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore
variable {G : Type*} [Group G]

/-- Cardinality of an actual flag subgroup, not merely of its coordinates. -/
theorem flagPreimage_card {V : Subgroup G} (e : V ≃* Multiplicative Natural)
    (P : Submodule (ZMod 2) Natural) :
    Nat.card (flagPreimage e P) = 2 ^ Module.finrank (ZMod 2) P := by
  let f : flagPreimage e P ≃ P :=
    { toFun := fun x => ⟨(e ⟨x.val, flagPreimage_le e P x.property⟩).toAdd,
        (mem_flagPreimage_iff e P _).mp x.property⟩
      invFun := fun w => ⟨(e.symm (Multiplicative.ofAdd w.val)).val,
        (mem_flagPreimage_iff e P _).mpr (by rw [e.apply_symm_apply]; exact w.property)⟩
      left_inv := by
        intro x
        apply Subtype.ext
        change (e.symm (e ⟨x.val, flagPreimage_le e P x.property⟩)).val = x.val
        exact congrArg Subtype.val (e.symm_apply_apply _)
      right_inv := by intro w; apply Subtype.ext; exact congrArg Multiplicative.toAdd (e.apply_symm_apply _) }
  rw [Nat.card_congr f, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card, ZMod.card]

namespace NaturalSetup
variable {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃)
include d

/-- Restriction of the actual LT action to its marked ordinary component. -/
theorem component_conjugation (l : L) (v : V) :
    (d.coordinate (V.normalizerMonoidHom
      ⟨l.val, d.normalizes_V (show l.val ∈ L ⊔ T from (show L ≤ L ⊔ T from le_sup_left) l.property)⟩ v)).toAdd =
      alternatingNaturalRepresentation (Fin 6) (d.model (QuotientGroup.mk' (pCore 2 L) l))
        (d.coordinate v).toAdd := by
  have h := d.conjugation (inclusion le_sup_left l) v
  rw [d.model_compatible] at h
  exact h

/-- The kernel of the natural L-action is exactly its two-core. -/
theorem component_centralizer : L ⊓ centralizer (V : Set G) = L.pCoreIn 2 := by
  have hiff (l : L) : l.val ∈ centralizer (V : Set G) ↔ l ∈ pCore 2 L := by
    constructor
    · intro hl
      apply (QuotientGroup.eq_one_iff l).mp
      apply d.model.injective
      rw [map_one]
      apply ComponentSieve.SixAndG2.NaturalSix.alternatingAction_injective
      apply LinearMap.ext
      intro w
      obtain ⟨v, hv⟩ := d.coordinate.surjective (Multiplicative.ofAdd w)
      have hv' : (d.coordinate v).toAdd = w := hv
      have hc : V.normalizerMonoidHom
          ⟨l.val, d.normalizes_V (show l.val ∈ L ⊔ T from (show L ≤ L ⊔ T from le_sup_left) l.property)⟩ v = v := by
        apply Subtype.ext
        change l.val * v.val * l.val⁻¹ = v.val
        rw [← mem_centralizer_iff.mp hl v.val v.property, mul_inv_cancel_right]
      have he := d.component_conjugation l v
      rw [hc, hv'] at he
      simpa only [ComponentSieve.SixAndG2.NaturalSix.alternatingAction, QuotientGroup.mk'_apply, map_one, Module.End.one_apply] using he.symm
    · intro hl
      apply mem_centralizer_iff.mpr
      intro v hv
      have he := d.component_conjugation l ⟨v, hv⟩
      have hq : QuotientGroup.mk' (pCore 2 L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
      rw [hq, map_one, map_one, Module.End.one_apply] at he
      have he' := congrArg Subtype.val (d.coordinate.injective he)
      change l.val * v * l.val⁻¹ = v at he'
      exact (mul_inv_eq_iff_eq_mul.mp he').symm
  apply le_antisymm
  · intro l hl
    exact ⟨⟨l, hl.1⟩, (hiff ⟨l, hl.1⟩).mp hl.2, rfl⟩
  · rintro _ ⟨l, hl, rfl⟩
    exact ⟨l.property, (hiff l).mpr hl⟩

/-- The source flag has the literal orders 2, 4 and 8. -/
theorem flag_orders : Nat.card V₁ = 2 ∧ Nat.card V₂ = 4 ∧ Nat.card V₃ = 8 := by
  have hp := (congrArg (fun A : Subgroup G => Nat.card A) d.line_eq).trans
    (flagPreimage_card d.coordinate d.point)
  have hd := (congrArg (fun A : Subgroup G => Nat.card A) d.plane_eq).trans
    (flagPreimage_card d.coordinate d.plane)
  have hh := (congrArg (fun A : Subgroup G => Nat.card A) d.seed_eq).trans
    (flagPreimage_card d.coordinate d.hyperplane)
  rw [d.point_dim] at hp
  rw [d.plane_dim] at hd
  rw [d.hyperplane_dim] at hh
  exact ⟨hp.trans (by decide), hd.trans (by decide), hh.trans (by decide)⟩

/-- The natural module has order sixteen. -/
theorem natural_order : Nat.card V = 16 := by
  rw [Nat.card_congr d.coordinate.toEquiv]
  change Nat.card Natural = 16
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_eq_fintype_card, ZMod.card,
    finrank_natural_even (Fin 6) (by decide)]
  norm_num

/-- The fixed subgroup is trivial, using the actual residual's cubic actor. -/
theorem fixed_subgroup [Finite G] : V ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨Q, hQ⟩ := d.image_sylow
  obtain ⟨c, hc, hf⟩ := PlaneGeometry.plane_residual_actor d.permutation.range
    d.alternating_le_range Q d.plane d.plane_dim (by rw [hQ]; exact d.sylow_plane_stable)
  rw [← d.two_image] at hc
  obtain ⟨a, ha, rfl⟩ := hc
  apply le_bot_iff.mp
  intro v hv
  let vV : V := ⟨v, hv.1⟩
  have hconj : V.normalizerMonoidHom ⟨a.val, d.normalizes_V a.property⟩ vV = vV := by
    apply Subtype.ext
    change a.val * v * a.val⁻¹ = v
    rw [mem_centralizer_iff.mp hv.2 a.val (localResidual_le L V₂ ha), mul_inv_cancel_right]
  have he := d.conjugation a vV
  rw [hconj] at he
  have hz := hf (d.coordinate vV).toAdd he.symm
  have hv1 : vV = 1 := d.coordinate.injective (hz.trans (map_one d.coordinate).symm)
  exact congrArg Subtype.val hv1

end NaturalSetup
end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore
