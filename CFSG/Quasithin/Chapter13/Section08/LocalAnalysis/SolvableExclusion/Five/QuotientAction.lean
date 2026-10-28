module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.DisjointSummands
public import Theory.GroupAction.SubgroupQuotientCommutatorImage

/-!
# The actual star action and its restricted commutator images

The five-primary calculation acts on the literal quotient U_H/V₁ through
H/O₂(H). Centralization by O₂(H) descends conjugation to this quotient.
For every X≤U_H and B≤H, the moved subgroup of the image of X is exactly
the image of [X,B]. In particular, moving a point of the second summand
makes that ambient commutator image nontrivial.

The proof lifts generators through both quotient maps. It needs only
relative normalization; no subgroup is assumed normal in the ambient G.
Faithfulness and the construction of the five-primary factors remain
source obligations, separate from the definition of `StarAction`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951, especially its final commutator contradiction.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- An action of the literal H/O₂(H) on the literal UH/V₁, with its
conjugation formula. Faithfulness is a separate source obligation. -/
structure StarAction (H UH V₁ : Subgroup G) [(V₁.subgroupOf UH).Normal] where
  normalizes : H ≤ normalizer (UH : Set G)
  action : Source.Hstar H →* MulAut (UH ⧸ V₁.subgroupOf UH)
  conjugation : ∀ h : H, ∀ u : UH,
    action (QuotientGroup.mk' (pCore 2 H) h)
        (QuotientGroup.mk' (V₁.subgroupOf UH) u) =
      QuotientGroup.mk' (V₁.subgroupOf UH)
        ⟨(h : G) * (u : G) * (h : G)⁻¹,
          (mem_normalizer_iff.mp (normalizes h.property) u).mp u.property⟩

/-- Descent through the actual two-core uses its centralization of UH/V₁. -/
theorem exists_starAction (H UH V₁ : Subgroup G) [(V₁.subgroupOf UH).Normal]
    (hn : H ≤ normalizer (UH : Set G))
    (hz : H ≤ normalizer (V₁ : Set G))
    (hcore : ⁅UH, Source.QH H⁆ ≤ V₁) : Nonempty (StarAction H UH V₁) := by
  obtain ⟨ρ, hρ⟩ := exists_quotient_conjugation_action H UH V₁ hn hz inferInstance
  have hk := quotient_conjugation_action_kills_commutator_layer H UH V₁
    (Source.QH H) inferInstance hn hcore ρ hρ
  have hQ : (Source.QH H).subgroupOf H = pCore 2 H :=
    comap_map_eq_self_of_injective H.subtype_injective _
  rw [hQ] at hk
  exact ⟨⟨hn, QuotientGroup.lift (pCore 2 H) ρ hk, hρ⟩⟩

namespace StarAction
variable {H UH V₁ : Subgroup G} [(V₁.subgroupOf UH).Normal]

/-- The subgroup acting on the quotient is the image of the actual B*. -/
def actors (a : StarAction H UH V₁) (B : Subgroup G) :
    Subgroup (MulAut (UH ⧸ V₁.subgroupOf UH)) := (Source.starImage H B).map a.action

theorem actors_eq (a : StarAction H UH V₁) (B : Subgroup G) :
    a.actors B = (B.subgroupOf H).map
      (a.action.comp (QuotientGroup.mk' (pCore 2 H))) := by
  exact map_map _ _ _

/-- Restricted moved spaces agree with the ambient commutator image.
This applies to the second factor U₂, without replacing its image by
the full quotient UH/V₁ or by an unrelated representation. -/
theorem commutatorSubgroup_eq_tildeImage (a : StarAction H UH V₁)
    (X B : Subgroup G) (hX : X ≤ UH) (hB : B ≤ H) :
    commutatorSubgroup (a.actors B) (UH ⧸ V₁.subgroupOf UH)
      (tildeImage UH V₁ X) = tildeImage UH V₁ ⁅X, B⁆ := by
  let q := QuotientGroup.mk' (V₁.subgroupOf UH)
  let ρ := a.action.comp (QuotientGroup.mk' (pCore 2 H))
  rw [a.actors_eq]
  change commutatorSubgroup ((B.subgroupOf H).map ρ) _ _ = _
  let C := commutatorSubgroup ((B.subgroupOf H).map ρ)
    (UH ⧸ V₁.subgroupOf UH) (tildeImage UH V₁ X)
  apply le_antisymm
  · rw [commutatorSubgroup, closure_le]
    rintro _ ⟨b, x, hx, rfl⟩
    obtain ⟨h, hh, heq⟩ := b.property
    obtain ⟨u, hu, rfl⟩ := hx
    change (q u)⁻¹ * (b : MulAut _) (q u) ∈ _
    rw [← heq]
    change (q u)⁻¹ * a.action (QuotientGroup.mk' (pCore 2 H) h) (q u) ∈ _
    rw [a.conjugation, ← map_inv, ← map_mul]
    apply mem_map_of_mem
    change (u : G)⁻¹ * ((h : G) * (u : G) * (h : G)⁻¹) ∈ ⁅X, B⁆
    simpa only [commutatorElement_def, inv_inv, mul_assoc, coe_subtype] using
      commutator_mem_commutator (X.inv_mem hu) hh
  · let preimage := (C.comap q).map UH.subtype
    have hcomm : ⁅X, B⁆ ≤ UH :=
      (commutator_mono hX le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hB.trans a.normalizes))
    have hbound : ⁅X, B⁆ ≤ preimage := by
      apply commutator_le.mpr
      intro x hx b hb
      let u : UH := ⟨x, hX hx⟩
      let h : H := ⟨b, hB hb⟩
      let actor : (B.subgroupOf H).map ρ := ⟨ρ h, mem_map_of_mem ρ hb⟩
      have hc : ⁅x, b⁆ ∈ UH := hcomm (commutator_mem_commutator hx hb)
      refine ⟨⟨⁅x, b⁆, hc⟩, ?_, rfl⟩
      have hm : (q u⁻¹)⁻¹ * (actor • q u⁻¹) ∈ C :=
        subset_closure ⟨actor, q u⁻¹, mem_map_of_mem q (X.inv_mem hx), rfl⟩
      have he : (q u⁻¹)⁻¹ * (actor • q u⁻¹) = q ⟨⁅x, b⁆, hc⟩ := by
        change (q u⁻¹)⁻¹ * a.action (QuotientGroup.mk' (pCore 2 H) h) (q u⁻¹) = _
        rw [a.conjugation, ← map_inv, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [coe_mul, coe_inv, inv_inv, commutatorElement_def, u, h, mul_assoc]
      change q ⟨⁅x, b⁆, hc⟩ ∈ C
      exact he ▸ hm
    rintro x ⟨u, hu, rfl⟩
    obtain ⟨v, hv, he⟩ := hbound hu
    exact (show v = u from Subtype.ext he) ▸ hv

/-- On the whole tilde quotient the same comparison identifies its moved
subgroup, so model cardinalities transfer to the ambient commutator image. -/
theorem commutatorAction_eq_tildeImage (a : StarAction H UH V₁)
    (B : Subgroup G) (hB : B ≤ H) :
    commutatorAction (a.actors B) (UH ⧸ V₁.subgroupOf UH) =
      tildeImage UH V₁ ⁅UH, B⁆ := by
  have ht : tildeImage UH V₁ UH = ⊤ := by
    unfold tildeImage
    rw [subgroupOf_self]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  simpa only [ht] using a.commutatorSubgroup_eq_tildeImage UH B le_rfl hB

/-- A nonfixed vector in the actual second summand gives a nontrivial
ambient commutator image. No faithfulness of an auxiliary action is assumed. -/
theorem commutator_image_ne_bot_of_moves (a : StarAction H UH V₁)
    (X B : Subgroup G) (hX : X ≤ UH) (hB : B ≤ H)
    (hmoves : ∃ b : a.actors B, ∃ x ∈ tildeImage UH V₁ X, b • x ≠ x) :
    tildeImage UH V₁ ⁅X, B⁆ ≠ ⊥ := by
  rw [← a.commutatorSubgroup_eq_tildeImage X B hX hB]
  intro he
  obtain ⟨b, x, hx, hn⟩ := hmoves
  have hm : x⁻¹ * (b • x) ∈ commutatorSubgroup (a.actors B)
      (UH ⧸ V₁.subgroupOf UH) (tildeImage UH V₁ X) :=
    subset_closure ⟨b, x, hx, rfl⟩
  rw [he, mem_bot] at hm
  exact hn (inv_mul_eq_one.mp hm).symm

end StarAction
end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
