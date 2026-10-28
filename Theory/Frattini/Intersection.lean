module

public import Theory.Frattini.PGroupMap
public import Theory.Frattini.OmegaProducts

/-!
# Frattini subgroups in intersections of finite p-groups

The Frattini subgroup of a common subgroup lies in both ambient Frattini
images. Disjoint images therefore force a trivial Frattini subgroup. The
proof uses functoriality under inclusions; injective transport also makes
the criterion apply to two conjugate p-subgroups.

This is the elementary p-group argument used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 12.8.11(2), printed p.854.
-/

open Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Frattini subgroups are monotone among finite p-subgroups, after inclusion
in their common ambient group. -/
public theorem frattini_image_le_of_le {A B : Subgroup G} (hAB : A ≤ B)
    (hB : IsPGroup p B) :
    (frattini A).map A.subtype ≤ (frattini B).map B.subtype := by
  let : Fact (IsPGroup p B) := ⟨hB⟩
  let : Fact (IsPGroup p A) := ⟨hB.of_injective (inclusion hAB) (inclusion_injective hAB)⟩
  have h := map_mono (f := B.subtype)
    (frattini_map_le_of_isPGroup (p := p) (inclusion hAB))
  simpa only [map_map, subtype_comp_inclusion] using h

/-- A common subgroup of finite p-subgroups whose ambient Frattini subgroups
are disjoint has trivial Frattini subgroup. -/
public theorem frattini_eq_bot_of_disjoint_images {A B D : Subgroup G}
    (hA : IsPGroup p A) (hB : IsPGroup p B) (hDA : D ≤ A) (hDB : D ≤ B)
    (hdis : Disjoint ((frattini A).map A.subtype) ((frattini B).map B.subtype)) :
    frattini D = ⊥ := by
  have hle : (frattini D).map D.subtype ≤ ⊥ :=
    (le_inf (frattini_image_le_of_le hDA hA)
      (frattini_image_le_of_le hDB hB)).trans hdis.le_bot
  apply bot_unique
  intro x hx
  apply D.subtype_injective
  exact (mem_bot.mp (hle (mem_map_of_mem D.subtype hx)))

omit [Finite G] in
/-- The ambient Frattini subgroup commutes with an injective change of group. -/
public theorem frattini_image_map {K : Type*} [Group K]
    (A : Subgroup G) (f : G →* K) (hf : Function.Injective f) :
    (frattini (A.map f)).map (A.map f).subtype =
      ((frattini A).map A.subtype).map f := by
  let e := A.equivMapOfInjective f hf
  rw [← frattini_map_equiv e, map_map, map_map]
  rfl
end Subgroup
