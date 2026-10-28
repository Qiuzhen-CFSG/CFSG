module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SeedIntersections

/-!
# Full centralizers of planes in the original HS seed

A plane containing the distinguished involution has centralizer inside its
centralizer H. The intersection theorem for H-conjugate seeds then forces
that entire plane centralizer into the original seed normalizer M. Full
seed fusion transports any plane to one containing the marked involution.

This controls the full ambient centralizer, as needed when constructing
elementary subgroups over a proper plane of the seed in I.4.8.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims

variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem plane_centralizer_marked (h : TypeAt z V)
    (W : Subgroup G) (hWV : W ≤ V) (hW4 : Nat.card W = 4) (hzW : z ∈ W) :
    centralizer (W : Set G) ≤ normalizer (V : Set G) := by
  intro g hg
  have hgH : g ∈ involutionCentralizer z := mem_centralizer_singleton_iff.mpr (hg z hzW).symm
  by_contra hgn
  have hW : W ≤ V ⊓ V.map (MulAut.conj g).toMonoidHom := by
    intro w hw
    refine ⟨hWV hw, w, hWV hw, ?_⟩
    change g * w * g⁻¹ = w
    rw [← hg w hw, mul_inv_cancel_right]
  rw [h.seed_conjugate_intersection g hgH hgn] at hW
  have hc := card_le_of_le hW
  rw [hW4, Nat.card_zpowers, h.involution] at hc
  omega

/-- The full ambient centralizer of every plane in the original seed lies
in that seed's actual normalizer. -/
theorem TypeAt.plane_centralizer_le_normalizer (h : TypeAt z V)
    (W : Subgroup G) (hWV : W ≤ V) (hW4 : Nat.card W = 4) :
    centralizer (W : Set G) ≤ normalizer (V : Set G) := by
  have hWne : W ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hW4
    norm_num at hW4
  obtain ⟨w, hw, hw1⟩ := W.bot_or_exists_ne_one.resolve_left hWne
  have hz1 : z ≠ 1 := by
    intro he
    have hh := h.involution
    simp [he] at hh
  obtain ⟨g, hg⟩ := h.seed_transitive ⟨w, hWV hw⟩ ⟨z, h.involution_mem_seed⟩
    (fun he => hw1 (congrArg Subtype.val he))
    (fun he => hz1 (congrArg Subtype.val he))
  let e := MulAut.conj (g : G)
  let Wg := W.map e.toMonoidHom
  have heV : V.map e.toMonoidHom = V := mem_normalizer_iff_map_conj_eq.mp g.property
  have hWgV : Wg ≤ V := heV ▸ map_mono (f := e.toMonoidHom) hWV
  have hWgc : Nat.card Wg = 4 := by
    rw [card_map_of_injective e.injective, hW4]
  have hzWg : z ∈ Wg := by
    refine ⟨w, hw, ?_⟩
    exact congrArg Subtype.val hg
  intro c hc
  have hcg : e c ∈ centralizer (Wg : Set G) := by
    rintro _ ⟨v, hv, rfl⟩
    change e v * e c = e c * e v
    simpa only [map_mul] using congrArg e (hc v hv)
  have hcm : e c ∈ normalizer (V : Set G) :=
    plane_centralizer_marked h Wg hWgV hWgc hzWg hcg
  have hh := (normalizer (V : Set G)).mul_mem
    ((normalizer (V : Set G)).mul_mem
      ((normalizer (V : Set G)).inv_mem g.property) hcm) g.property
  simpa only [e, MulAut.conj_apply, inv_mul_cancel_left, mul_assoc,
    inv_mul_cancel, mul_one] using hh

end CFSG.Quasithin.HigmanSims
