module
public import Theory.Frattini.Intersection

/-!
# Elementary common subgroups inside an arbitrary ambient group

A subgroup of two finite p-groups with disjoint ambient Frattini images has
trivial Frattini subgroup and is elementary abelian. Only the finite subgroups
are required to be finite; the ambient group may be an infinite amalgam.
This form applies to the paired critical orbits in MS93 (3.6), p.871.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

private theorem finite_frattini_image_le_of_le {A B : Subgroup G}
    [Finite A] [Finite B] (hAB : A ≤ B) (hB : IsPGroup p B) :
    (frattini A).map A.subtype ≤ (frattini B).map B.subtype := by
  let : Fact (IsPGroup p B) := ⟨hB⟩
  let : Fact (IsPGroup p A) := ⟨hB.of_injective (inclusion hAB) (inclusion_injective _)⟩
  have h := map_mono (f := B.subtype) (frattini_map_le_of_isPGroup (p := p) (inclusion hAB))
  simpa only [map_map,subtype_comp_inclusion] using h

theorem finite_common_subgroup_elementary_of_disjoint_frattini
    {A B D : Subgroup G} [Finite A] [Finite B]
    (hA : IsPGroup p A) (hB : IsPGroup p B) (hDA : D ≤ A) (hDB : D ≤ B)
    (hdis : Disjoint ((frattini A).map A.subtype) ((frattini B).map B.subtype)) :
    IsElementaryAbelian p D := by
  let : Finite D := Finite.of_injective (inclusion hDA) (inclusion_injective _)
  let : Fact (IsPGroup p D) := ⟨hA.of_injective (inclusion hDA) (inclusion_injective _)⟩
  have hh : (frattini D).map D.subtype ≤ ⊥ :=
    (le_inf (finite_frattini_image_le_of_le hDA hA)
      (finite_frattini_image_le_of_le hDB hB)).trans hdis.le_bot
  have he : frattini D = ⊥ := by
    apply bot_unique
    intro x hx
    exact mem_bot.mpr (D.subtype_injective (mem_bot.mp (hh (mem_map_of_mem D.subtype hx))))
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := p)).mp he
end Subgroup
