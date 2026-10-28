module

public import CFSG.Quasithin.ChapterF.Section09.Basic
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.CommutatorPreimageFrattini
public import Theory.ElementaryAbelian.VectorSpace

/-!
# The faithful binary action for the nonabelian branch of 13.5.20

The denominator V₁ is normal relative to U_H because H centralizes it.
F.9.2 bounds the Frattini subgroup by V₁, so the literal quotient U_H/V₁
is elementary abelian, even when U_H is nonabelian. Conjugation descends
through H/O₂(H): its kernel is exactly the already proved F.9.2 kernel.
The resulting binary action retains the representative conjugation formula.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
F.9.1–2, printed pp.317–318; 13.5.20, printed p.923.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction
open Section08.Source
variable {G : Type*} [Group G] [Finite G]
variable {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
include h

theorem point_normal_in_UH : (D.V₁.subgroupOf D.UH).Normal :=
  normal_subgroupOf_of_le_normalizer (h.UH_le_H.trans
    (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))

abbrev Quotient := D.UH ⧸ D.V₁.subgroupOf D.UH

theorem quotient_elementary :
    let : (D.V₁.subgroupOf D.UH).Normal := point_normal_in_UH h
    IsElementaryAbelian 2 (Quotient (D := D)) := by
  let : (D.V₁.subgroupOf D.UH).Normal := point_normal_in_UH h
  apply elementary_quotient_of_frattini_le (show IsPGroup 2 D.UH from h.g2_hypothesis.U_isPGroup)
    (D.V₁.subgroupOf D.UH)
  intro x hx
  exact h.frattini_UH_le_point (mem_map_of_mem D.UH.subtype hx)

section
variable [hn : (D.V₁.subgroupOf D.UH).Normal]

private theorem action_exists :
    ∃ a : Hstar D.H →* MulAut (Quotient (D := D)),
      Function.Injective a ∧
      ∀ (x : D.H) (u : D.UH),
      a (QuotientGroup.mk' (pCore 2 D.H) x)
        (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u) =
      QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
        ⟨(x : G) * u * (x : G)⁻¹,
          le_normalizer_iff.mp (le_normalizer_conjugateSpanBy D.Vplus D.H)
            x x.property u u.property⟩ := by
  let nU := le_normalizer_conjugateSpanBy D.Vplus D.H
  obtain ⟨α, hα⟩ := exists_quotient_conjugation_action D.H D.UH D.V₁ nU
    (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) hn
  have hk : α.ker = pCore 2 D.H := by
    apply le_antisymm
    · intro x hx
      have hxc : (x : G) ∈ h.kernel D.UH := by
        apply (h.mem_kernel_iff h.UH_le_H).mpr
        refine ⟨x.property, ?_⟩
        intro u hu
        have he := congrArg (fun f : MulAut (Quotient (D := D)) =>
          f (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) ⟨u, hu⟩)) hx
        rw [hα] at he
        have hc : ⁅(x : G), u⁆ ∈ D.V₁ := by
          simpa only [commutatorElement_def, div_eq_mul_inv, mem_subgroupOf, coe_mul, coe_inv, coe_mk] using
            (QuotientGroup.eq_iff_div_mem.mp he :
              (⟨(x : G) * u * (x : G)⁻¹, _⟩ : D.UH) / ⟨u, hu⟩ ∈ D.V₁.subgroupOf D.UH)
        simpa only [commutatorElement_inv] using D.V₁.inv_mem hc
      rw [h.kernel_UH_eq_QH] at hxc
      exact (comap_map_eq_self_of_injective D.H.subtype_injective (pCore 2 D.H)).le hxc
    · have hc := quotient_conjugation_action_kills_commutator_layer D.H D.UH D.V₁ D.QH
        hn nU h.commutator_UH_QH_le_point α hα
      have he : D.QH.subgroupOf D.H = pCore 2 D.H :=
        comap_map_eq_self_of_injective D.H.subtype_injective _
      rwa [he] at hc
  let β := QuotientGroup.lift (pCore 2 D.H) α (fun x hx => hk.symm ▸ hx)
  refine ⟨β, ?_, hα⟩
  apply (MonoidHom.ker_eq_bot_iff β).mp
  apply bot_unique
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 D.H) x
  exact (QuotientGroup.eq_one_iff y).mpr (hk ▸ hx)

variable [IsElementaryAbelian 2 (Quotient (D := D))]

omit h in
private def linearize (a : Hstar D.H →* MulAut (Quotient (D := D))) :
    Representation (ZMod 2) (Hstar D.H) (Additive (Quotient (D := D))) where
  toFun x := (a x).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext u
    change a 1 u.toMul = u.toMul
    rw [map_one]; rfl
  map_mul' x y := by
    ext u
    change a (x * y) u.toMul = a x (a y u.toMul)
    rw [map_mul]; rfl

theorem exists_representation :
    ∃ ρ : Representation (ZMod 2) (Hstar D.H) (Additive (Quotient (D := D))),
      Function.Injective ρ ∧
      ∀ (x : D.H) (u : D.UH),
        ρ (QuotientGroup.mk' (pCore 2 D.H) x)
          (Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u)) =
        Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
          ⟨(x : G) * u * (x : G)⁻¹,
            le_normalizer_iff.mp (le_normalizer_conjugateSpanBy D.Vplus D.H)
              x x.property u u.property⟩) := by
  obtain ⟨a, ha, hrep⟩ := action_exists h
  refine ⟨linearize a, ?_, hrep⟩
  intro x y he
  apply ha
  ext u
  exact congrArg (fun f => f (Additive.ofMul u)) he

/-- A chosen representation on the actual quotient, with no model replacement. -/
noncomputable def representation :
    Representation (ZMod 2) (Hstar D.H) (Additive (Quotient (D := D))) :=
  Classical.choose (exists_representation h)

theorem representation_injective : Function.Injective (representation h) :=
  (Classical.choose_spec (exists_representation h)).1

theorem representation_apply (x : D.H) (u : D.UH) :
    representation h (QuotientGroup.mk' (pCore 2 D.H) x)
      (Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u)) =
    Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
      ⟨(x : G) * u * (x : G)⁻¹,
        le_normalizer_iff.mp (le_normalizer_conjugateSpanBy D.Vplus D.H)
          x x.property u u.property⟩) :=
  (Classical.choose_spec (exists_representation h)).2 x u

end
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction
