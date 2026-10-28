module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.LocalStructure

/-!
# The literal fusion intersection in the nonnormal quaternion branch

We use left conjugation throughout: the paper's `Qᵍ` is represented here by
the image of Q under `x ↦ g*x*g⁻¹`, with the same convention for `zᵍ`.
The saturation condition is the exact equality `E# = zᴳ ∩ Q`, where
`E = Q ∩ Qᵍ`. In the saturated case, invariance of the ambient conjugacy class
already shows that E is normal in H; global normality is a later source step.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), Sections 2–3, especially Lemma 2.8; Aschbacher–Smith I.4.6, p.417.
-/

@[expose] public section

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition

open Subgroup

variable {G : Type*} [Group G] {z : G}

/-- The actual intersection of Q with its left conjugate by `g`. -/
def coreIntersection (z g : G) : Subgroup G :=
  coreInG z ⊓ (coreInG z).map (MulAut.conj g).toMonoidHom

/-- The actual ambient conjugacy class of z intersected with Q. -/
abbrev CoreFusion (z : G) := {x : G // x ∈ coreInG z ∧ IsConj z x}

/-- The exceptional fusion pattern `E# = zᴳ ∩ Q` in source Lemma 2.8. -/
def FusionSaturated (z g : G) : Prop :=
  ∀ x : G, (x ∈ coreIntersection z g ∧ x ≠ 1) ↔
    (x ∈ coreInG z ∧ IsConj z x)

/-- The local intersection and normalizer facts of source 2.4–2.6.
These are inputs to the later source arguments, not assumed in I.4.6. -/
structure IntersectionData (z g : G) : Prop where
  elementary : IsElementaryAbelian 2 (coreIntersection z g)
  card : Nat.card (coreIntersection z g) = 8
  normal_in_centralizer : ((coreIntersection z g).subgroupOf (Centralizer z)).Normal
  self_centralizing : centralizer (coreIntersection z g : Set G) = coreIntersection z g
  normalizer_quotient : Nonempty
    ((normalizer (coreIntersection z g : Set G) ⧸
      (coreIntersection z g).subgroupOf (normalizer (coreIntersection z g : Set G))) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
  involution_fusion : ∀ t : G, t ∈ Centralizer z → orderOf t = 2 →
    ∃ m : normalizer (coreIntersection z g : Set G),
      (m : G) * t * (m : G)⁻¹ ∈ coreInG z
  centralizer_odd_index : Odd (Centralizer z).index

theorem coreIntersection_le (z g : G) : coreIntersection z g ≤ coreInG z := inf_le_left

theorem conjugate_mem_coreIntersection [Finite G] (h : Hypotheses z) (g : G)
    (hg : g * z * g⁻¹ ∈ coreInG z) : g * z * g⁻¹ ∈ coreIntersection z g :=
  ⟨hg, mem_map_of_mem (MulAut.conj g).toMonoidHom h.involution_mem_coreInG⟩

/-- The source fusion witness gives genuinely distinct conjugate cores. -/
theorem conjugate_core_ne [Finite G] (h : Hypotheses z) (g : G)
    (hg : g * z * g⁻¹ ≠ z) :
    (coreInG z).map (MulAut.conj g).toMonoidHom ≠ coreInG z := by
  intro he
  have hn : g ∈ normalizer (coreInG z : Set G) := mem_normalizer_iff_map_conj_eq.mpr he
  rw [h.normalizer_core] at hn
  exact hg (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hn))

/-- Membership includes the identity separately from the source's sharp set. -/
theorem FusionSaturated.mem_iff {g : G} (hs : FusionSaturated z g) (x : G) :
    x ∈ coreIntersection z g ↔ x = 1 ∨ (x ∈ coreInG z ∧ IsConj z x) := by
  constructor
  · intro hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr ((hs x).mp ⟨hx, hx1⟩)
  · rintro (rfl | hx)
    · exact (coreIntersection z g).one_mem
    · exact ((hs x).mpr hx).1

/-- In the saturated case E is normal in the involution centralizer H.
This is the first assertion used in the proof of source Lemma 2.8. -/
theorem FusionSaturated.normal_in_centralizer [Finite G] (h : Hypotheses z)
    {g : G} (hs : FusionSaturated z g) :
    ((coreIntersection z g).subgroupOf (Centralizer z)).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer
    ((coreIntersection_le z g).trans (coreInG_le z))).mpr
  intro a ha
  have haN : a ∈ normalizer (coreInG z : Set G) := h.normalizer_core.symm ▸ ha
  intro x
  change x ∈ coreIntersection z g ↔ a * x * a⁻¹ ∈ coreIntersection z g
  have hconj : IsConj z (a * x * a⁻¹) ↔ IsConj z x := by
    have hx : IsConj x (a * x * a⁻¹) := isConj_iff.mpr ⟨a, rfl⟩
    exact ⟨fun hc => hc.trans hx.symm, fun hc => hc.trans hx⟩
  rw [hs.mem_iff, hs.mem_iff, hconj]
  have he : a * x * a⁻¹ = 1 ↔ x = 1 := by
    change (MulAut.conj a) x = 1 ↔ x = 1
    exact (MulAut.conj a).map_eq_one_iff
  have hQ : x ∈ coreInG z ↔ a * x * a⁻¹ ∈ coreInG z := haN x
  rw [he, ← hQ]

/-- Transfer the local normalizer quotient through its literal embedding when
the global part of source 2.8 proves that this normalizer is all of G. -/
theorem IntersectionData.elementaryEight_of_normalizer_eq_top {g : G}
    (d : IntersectionData z g)
    (hM : normalizer (coreIntersection z g : Set G) = ⊤) :
    ElementaryEightAlternative G := by
  let E := coreIntersection z g
  let M := normalizer (E : Set G)
  have hn : E.Normal := normalizer_eq_top_iff.mp hM
  have hMtop : M = ⊤ := hM
  let inclusion : M ≃* G := MulEquiv.ofBijective M.subtype
    ⟨M.subtype_injective, fun x => ⟨⟨x, hMtop.symm ▸ mem_top x⟩, rfl⟩⟩
  have hm : (E.subgroupOf M).map inclusion.toMonoidHom = E := by
    change (E.subgroupOf M).map M.subtype = E
    exact map_subgroupOf_eq_of_le E.le_normalizer
  obtain ⟨model⟩ := d.normalizer_quotient
  exact ⟨E, hn, d.elementary, d.card,
    ⟨(QuotientGroup.congr (E.subgroupOf M) E inclusion hm).symm.trans model⟩⟩

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition

end
