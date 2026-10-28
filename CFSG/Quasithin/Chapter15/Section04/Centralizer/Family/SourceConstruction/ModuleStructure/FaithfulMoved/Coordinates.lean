module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure.FaithfulMoved
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure.BinaryNormalizer.DoublePlane
/-!
# Orthogonal coordinates for the original local action

The source member X acts faithfully on its moved binary group by the preceding
module. Every element of M intertwines that action with conjugation on the
original image of X in M/O₂(M), hence normalizes its faithful automorphism image.
The full binary normalizer calculation therefore supplies orthogonal coordinates
for every original M-conjugation at once. The cubic image becomes exactly the
model rotation group, retaining the marking needed to recover the source factors.

This is the representation input for the Baumann pair-stabilization step in
Aschbacher--Smith, 15.4.12(6), printed pp.1160--1161, combined manuscript of
1 March 2004. It does not identify the whole quotient with the full normalizer.
-/

@[expose] public section

open Subgroup Stellmacher
open OrthogonalFourBinary.TerminalLines
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure
open BinaryNormalizer

private theorem range_normalized {A W H : Type*} [Group A] [Group W] [Group H]
    (ρ : A →* MulAut W) (α : H →* MulAut A) (β : H →* MulAut W)
    (he : ∀ g a w, β g (ρ a w) = ρ (α g a) (β g w)) (g : H) :
    β g ∈ normalizer (ρ.range : Set (MulAut W)) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hh : (MulAut.conj (β g)).toMonoidHom.comp ρ = ρ.comp (α g).toMonoidHom := by
    ext a w
    change β g (ρ a ((β g)⁻¹ w)) = ρ (α g a) w
    rw [he]
    simp only [MulAut.apply_inv_self]
  rw [MonoidHom.map_range]
  change ((MulAut.conj (β g)).toMonoidHom.comp ρ).range = ρ.range
  rw [hh, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (α g).surjective,
    ← MonoidHom.range_eq_map]

/-- Compatible normalizer coordinates on the actual moved group, including
all original M-conjugations and the marked cubic image. -/
theorem Input.double_orthogonal_action {G : Type*} [Group G] [Finite G]
    {K : GroupClass} {T : Sylow 2 G} {M X : Subgroup G} (h : Input K T M X 2) :
    ∃ (c : movedModule (T : Subgroup G) M X ≃* ModelSpace)
      (γ : M →* OrthogonalFourBinary.IsometryGroup)
      (ρ : image M X →* MulAut (movedModule (T : Subgroup G) M X)),
      Function.Injective ρ ∧
      (∀ (x : X) (w : movedModule (T : Subgroup G) M X),
        (ρ (memberProjection M X h.member_le x) w : G) =
          (x : G) * (w : G) * (x : G)⁻¹) ∧
      ρ.range.map (MulAut.congr c).toMonoidHom = modelRotations ∧
      (∀ (m : M) (w : movedModule (T : Subgroup G) M X),
        (c.symm (vectorAction (γ m) (c w)) : G) =
          (m : G) * (w : G) * (m : G)⁻¹) := by
  let W := movedModule (T : Subgroup G) M X
  let : IsElementaryAbelian 2 W := h.moved_elementary
  obtain ⟨ρ,hρinj,hρ⟩ := h.faithful_moved_action
  let α := imageConjugation M X ((normal_subgroupOf_iff_le_normalizer h.member_le).mp h.normal)
  let β := moduleConjugation M W h.moved_normalized
  have he : ∀ g a w, β g (ρ a w) = ρ (α g a) (β g w) :=
    source_intertwining M X W h.member_le
      ((normal_subgroupOf_iff_le_normalizer h.member_le).mp h.normal)
      h.moved_normalized ρ hρ
  let βN : M →* normalizer (ρ.range : Set (MulAut W)) :=
    β.codRestrict _ (range_normalized ρ α β he)
  have hW : Nat.card W = 16 := by simpa using h.moved_card
  have hA : Nat.card ρ.range = 9 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv]
    simpa using h.image_structure.2
  obtain ⟨c,e,hc,hce⟩ := double_normalizer_coordinates hW ρ.range hA
  refine ⟨c,e.toMonoidHom.comp βN,ρ,hρinj,hρ,hc,?_⟩
  intro m w
  have hh := congrArg c.symm (hce (βN m) w)
  rw [c.symm_apply_apply] at hh
  exact (congrArg Subtype.val hh).symm
end CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure
