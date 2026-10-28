module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.Basic

/-!
# From full displacement to the literal tilde-group commutator

Pull the group commutator back through Action.tildeMap to a binary
subspace. Every linear displacement lands in that subspace, by conjugation
on the original representatives. Full displacement then gives the required
containment, while normalization supplies its reverse.

This works for the original possibly nonabelian U_H: only U_H/V₁ is
assumed elementary abelian. It constructs neither a splitting nor a model
identification. The final application isolates the exact linear equality
the concrete models must supply for 13.5.21(6) and hence 13.5.14.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.21(6), printed p.924 (PDF p.941).
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics
open Section08.Source
open scoped commutatorElement IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- Full linear displacement gives the required commutator in the original
ambient tilde quotient, without a splitting of U_H. -/
theorem tilde_generation_of_linear (B : Subgroup G) (hBH : B ≤ D.H)
    (hgen : subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H B) = ⊤) :
    D.tilde D.UH = ⁅D.tilde D.UH, D.tilde B⁆ := by
  let : (D.V₁.subgroupOf D.g2.G₁).Normal := D.g2.point_normal
  let C := ⁅D.tilde D.UH, D.tilde B⁆
  let J := C.comap (Action.tildeMap D h)
  let W : Submodule (ZMod 2) (Action.Space D) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup J)
  have hBW : subspaceCommutator (Action.starRepresentation D h) ⊤ (starImage D.H B) ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, ⟨b, hb, rfl⟩, w, _, rfl⟩
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (D.V₁.subgroupOf D.UH) w.toMul
    have he : Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u) = w :=
      congrArg Additive.ofMul hu
    rw [← he, Action.starRepresentation_apply, sub_eq_add_neg]
    change Action.tildeMap D h
      (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) _ *
        (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u)⁻¹) ∈ C
    rw [map_mul, map_inv]
    let q := QuotientGroup.mk' (D.V₁.subgroupOf D.g2.G₁)
    have hbG : b.val ∈ D.g2.G₁ := h.g2_hypothesis.H_le b.property
    let bG : D.g2.G₁ := ⟨b.val, hbG⟩
    let uG := inclusion (Action.UH_le_ambient D h) u
    have hbT : q bG ∈ D.tilde B := ⟨bG, hb, rfl⟩
    have huT : q uG ∈ D.tilde D.UH := ⟨uG, u.property, rfl⟩
    have hc : ⁅q bG, q uG⁆ ∈ C := by
      change ⁅q bG, q uG⁆ ∈ ⁅D.tilde D.UH, D.tilde B⁆
      rw [commutator_comm]
      exact commutator_mem_commutator hbT huT
    convert hc using 1
    apply Iff.of_eq
    apply congrArg (fun x : D.Tilde => x ∈ C)
    change q (bG * uG * bG⁻¹) * (q uG)⁻¹ = _
    simp only [map_mul, map_inv, commutatorElement_def]
  have htop : W = ⊤ := top_unique (hgen ▸ hBW)
  have hUC : D.tilde D.UH ≤ C := by
    intro x hx
    obtain ⟨u, hu⟩ := (Action.tildeEquiv D h).surjective ⟨x, hx⟩
    have hw : Additive.ofMul u ∈ W := by rw [htop]; trivial
    have he : Action.tildeMap D h u = x := congrArg Subtype.val hu
    exact he ▸ hw
  have hnorm : B.subgroupOf D.g2.G₁ ≤ normalizer (D.UH.subgroupOf D.g2.G₁ : Set D.g2.G₁) := by
    rw [← subgroupOf_normalizer_eq (Action.UH_le_ambient D h)]
    exact comap_mono (hBH.trans (le_normalizer_conjugateSpanBy D.Vplus D.H))
  have htn : D.tilde B ≤ normalizer (D.tilde D.UH : Set D.Tilde) :=
    (map_mono hnorm).trans (le_normalizer_map _)
  exact le_antisymm hUC (le_normalizer_iff_commutator_le_left.mp htn)

/-- Application to the original L₁ in 13.5.21(6), retaining the tilde map
used by 13.5.14. The model must establish full linear displacement. -/
theorem local_tilde_generation_of_linear
    (hgen : subspaceCommutator (Action.starRepresentation D h) ⊤
      (starImage D.H D.L₁) = ⊤) :
    D.tilde D.UH = ⁅D.tilde D.UH, D.tilde D.L₁⁆ :=
  tilde_generation_of_linear D h D.L₁ (le_sup_left.trans h.local_le) hgen

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.AlternatingParabolics
