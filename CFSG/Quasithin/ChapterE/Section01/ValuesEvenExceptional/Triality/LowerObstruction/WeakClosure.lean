module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.LowerObstruction.HeadFamily
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# Nontrivial weak closure and its proper normalizer

Sylow alignment puts the actual cubic-root actor into the prescribed T.
Its automorphism family therefore has nonidentity weak closure inside L∩T.
When L is simple, that weak closure cannot be normal in G: normality would
make it all of L, although the aligned positive subgroup lies in a proper
root parabolic. Thus its normalizer is proper, including for f=1.

This proves properness only. Containment of this normalizer and all smaller
bound E-members in one proper subgroup remains the lower-obstruction problem.
Source: Aschbacher--Smith E.1.5 and E.1.14(2), printed pp.210 and 214.
-/

public section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction
open Subgroup
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
variable {G : Type*} [Group G] {f : ℕ} {hf : 0 < f}

theorem aligned_unipotent_map (L : Subgroup G) (T : Sylow 2 G)
    (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf)) :
    (unipotent (binaryParameters f hf)).map (modelEmbedding L e) =
      (T : Subgroup G) ⊓ L := by
  rw [← he, Subgroup.map_map]
  have hc : (modelEmbedding L e).comp e.toMonoidHom = L.subtype := by
    ext x
    change (e.symm (e x) : G) = x
    rw [e.symm_apply_apply]
  rw [hc, subgroupOf_map_subtype]

theorem head_weakClosure_le_socle (L : Subgroup G) (T : Sylow 2 G)
    (e : L ≃* BinaryCarrier f hf) :
    weakClosure (T : Subgroup G) (ambientHeadFamily L e) ≤ L :=
  sSup_le fun _ h => ambientHeadFamily_le h.1

theorem head_weakClosure_ne_bot (L : Subgroup G) (T : Sylow 2 G)
    (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf)) :
    weakClosure (T : Subgroup G) (ambientHeadFamily L e) ≠ ⊥ := by
  let A := (headSubgroup (binaryParameters f hf) rfl).map (modelEmbedding L e)
  have hA : A ∈ ambientHeadFamily L e :=
    ⟨headSubgroup (binaryParameters f hf) rfl, headSubgroup_mem, rfl⟩
  have hAT : A ≤ (T : Subgroup G) := by
    have h := Subgroup.map_mono (f := modelEmbedding L e)
      (headSubgroup_le_unipotent (binaryParameters f hf) rfl)
    rw [aligned_unipotent_map L T e he] at h
    exact h.trans inf_le_left
  intro hz
  have hAb : A = ⊥ := bot_unique (hz ▸ le_sSup ⟨hA, hAT⟩)
  have hc := ambientHeadFamily_card hA
  rw [hAb, Nat.card_unique] at hc
  have hp : 1 < 2 ^ (5 * f) := one_lt_pow₀ (by decide) (by omega)
  omega

theorem head_weakClosure_normalizer_ne_top (L : Subgroup G) [IsSimpleGroup L]
    (T : Sylow 2 G) (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf)) :
    normalizer (weakClosure (T : Subgroup G) (ambientHeadFamily L e) : Set G) ≠ ⊤ := by
  let W := weakClosure (T : Subgroup G) (ambientHeadFamily L e)
  have hWL : W ≤ L := head_weakClosure_le_socle L T e
  have hWmap : (W.subgroupOf L).map L.subtype = W := map_subgroupOf_eq_of_le hWL
  intro htop
  let _ : W.Normal := normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.subgroupOf L) inferInstance with h | h
  · have hz : W = ⊥ := by rw [← hWmap, h, Subgroup.map_bot]
    exact head_weakClosure_ne_bot L T e he hz
  · have hLW : L = W := by
      rw [← hWmap, h, ← MonoidHom.range_eq_map, L.range_subtype]
    have hLT : L ≤ (T : Subgroup G) := hLW ▸ weakClosure_le _ _
    have hT : (T : Subgroup G).subgroupOf L = ⊤ :=
      top_unique (fun x _ => hLT x.property)
    rw [hT, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr e.surjective] at he
    apply parabolic_ne_top_binary (binaryParameters f hf) rfl Node.central
    apply top_unique
    rw [he]
    exact (unipotent_le_borel _).trans (borel_le_parabolic _ _)

end CFSG.Quasithin.ChapterE.ExceptionalValues.Triality.LowerObstruction
