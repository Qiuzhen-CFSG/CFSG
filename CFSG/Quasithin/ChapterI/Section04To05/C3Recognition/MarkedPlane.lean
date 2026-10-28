module

public import CFSG.Quasithin.ChapterI.Section04To05.C3Recognition.Source
public import Theory.SpecificGroups.SymplecticSix.FixedRadical

/-!
# The original plane inside the recognized symplectic six-space

The seven original Fano-plane points span a totally isotropic subspace.
Their distinct nonzero images give at least eight vectors including zero,
while total isotropy bounds its dimension by three. Thus they are exactly
its seven nonzero vectors. This retains the original plane incidence in
the recognition marking and supplies the natural three-space action of
the original plane vertex, needed in the source 13.7.5–6 application.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.C3Recognition
open Matrix Theory.LinearAlgebra Theory.SpecificGroups.SymplecticSix
open Theory.SpecificGroups.SymplecticSix.TwoLocalCover
variable {G : Type*} [Group G] {S : DSystem .C3 G}
namespace SymplecticMark
variable (m : SymplecticMark S)

def planeSpace (π : S.Plane) : Submodule (ZMod 2) (Vector (ZMod 2)) :=
  Submodule.span (ZMod 2) {v | ∃ x : S.Point, S.Inc x π ∧ m.point x = v}

theorem point_mem_planeSpace {π : S.Plane} {x : S.Point} (hx : S.Inc x π) :
    m.point x ∈ m.planeSpace π := Submodule.subset_span ⟨x, hx, rfl⟩

theorem planeSpace_isotropic (π : S.Plane) :
    ∀ u ∈ m.planeSpace π, ∀ v ∈ m.planeSpace π, form (ZMod 2) u v = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨y, hy, rfl⟩ := hv
      exact (m.orthogonal x y).mpr (S.collinear_of_common_plane hx hy)
    | zero => simp
    | add v w hv hw hv0 hw0 => simp only [map_add, hv0, hw0, add_zero]
    | smul a v hv hv0 => simp only [map_smul, hv0, smul_zero]
  | zero => simp
  | add u w hu hw hu0 hw0 =>
    intro v hv
    simp only [map_add, LinearMap.add_apply, hu0 v hv, hw0 v hv, add_zero]
  | smul a u hu hu0 =>
    intro v hv
    simp only [map_smul, LinearMap.smul_apply, hu0 v hv, smul_zero]

def planePointOptionMap (π : S.Plane) :
    Option {x : S.Point // S.Inc x π} → m.planeSpace π
  | none => 0
  | some x => ⟨m.point x.val, m.point_mem_planeSpace x.property⟩

theorem planePointOptionMap_injective (π : S.Plane) :
    Function.Injective (m.planePointOptionMap π) := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => exact (m.point_nonzero b.val (congrArg Subtype.val h).symm).elim
  | some a =>
    cases b with
    | none => exact (m.point_nonzero a.val (congrArg Subtype.val h)).elim
    | some b =>
      have h' := m.point_injective (congrArg Subtype.val h)
      exact congrArg some (Subtype.ext h')

theorem planeSpace_finrank (π : S.Plane) :
    Module.finrank (ZMod 2) (m.planeSpace π) = 3 := by
  have hle := finrank_le_three_of_isotropic (m.planeSpace π) (m.planeSpace_isotropic π)
  obtain ⟨r⟩ := S.exists_fanoPlaneResidue π
  have hp := r.card_points
  let : Finite {x : S.Point // S.Inc x π} := Nat.finite_of_card_ne_zero (by rw [hp]; decide)
  have hc := Nat.card_le_card_of_injective (m.planePointOptionMap π) (m.planePointOptionMap_injective π)
  rw [Finite.card_option, hp, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  have hge : 3 ≤ Module.finrank (ZMod 2) (m.planeSpace π) := by
    by_contra! h
    interval_cases hd : Module.finrank (ZMod 2) (m.planeSpace π) <;> norm_num [hd] at hc
  omega

theorem planeSpace_card (π : S.Plane) : Nat.card (m.planeSpace π) = 8 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, m.planeSpace_finrank]
  rfl

theorem mem_planeSpace_iff (π : S.Plane) (v : Vector (ZMod 2)) :
    v ∈ m.planeSpace π ↔ v = 0 ∨ ∃ x : S.Point, S.Inc x π ∧ m.point x = v := by
  constructor
  · intro hv
    obtain ⟨r⟩ := S.exists_fanoPlaneResidue π
    have hp := r.card_points
    let : Finite {x : S.Point // S.Inc x π} := Nat.finite_of_card_ne_zero (by rw [hp]; decide)
    have hs := (m.planePointOptionMap_injective π).bijective_of_nat_card_le (by
      rw [m.planeSpace_card, Finite.card_option, hp])
    obtain ⟨x, hx⟩ := hs.2 ⟨v, hv⟩
    cases x with
    | none => exact Or.inl (congrArg Subtype.val hx).symm
    | some x => exact Or.inr ⟨x.val, x.property, congrArg Subtype.val hx⟩
  · rintro (rfl | ⟨x, hx, rfl⟩)
    · exact Submodule.zero_mem _
    · exact m.point_mem_planeSpace hx

theorem point_mem_planeSpace_iff (π : S.Plane) (x : S.Point) :
    m.point x ∈ m.planeSpace π ↔ S.Inc x π := by
  rw [m.mem_planeSpace_iff]
  constructor
  · rintro (h | ⟨y, hy, he⟩)
    · exact (m.point_nonzero x h).elim
    · exact m.point_injective he ▸ hy
  · intro h
    exact Or.inr ⟨x, h, rfl⟩

theorem planeSpace_orthogonal (π : S.Plane) :
    (form (ZMod 2)).orthogonal (m.planeSpace π) = m.planeSpace π := by
  apply (Submodule.eq_of_le_of_finrank_eq
    (show m.planeSpace π ≤ (form (ZMod 2)).orthogonal (m.planeSpace π) from
      fun u hu v hv => m.planeSpace_isotropic π v hv u hu) ?_).symm
  rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate, m.planeSpace_finrank]
  simp [Theory.SpecificGroups.SymplecticSix.Vector]

end SymplecticMark
end Quasithin.I5.C3Recognition
