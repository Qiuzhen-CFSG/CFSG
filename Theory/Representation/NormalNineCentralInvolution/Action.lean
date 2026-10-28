module
public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual.Coordinates
public import Theory.Representation.AffineNine.Model

/-!
# The actual conjugation image on a normal elementary nine-group

Two-perfectness and nontrivial action of the original two-core force the
image of Y in GL₂(3) to be SL₂(3). The centralizer of that image consists
of the scalar matrices. Consequently any subgroup centralizing Y and
moving P contains an element inverting P. Coordinates retain both the
original subgroup embedding and its conjugation equation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.5.20, printed p.923 (PDF p.940).
-/

public section
open Subgroup Matrix
open Matrix.GeneralLinearGroup
open scoped IsMulCommutative
namespace Representation.NormalNineCentralInvolution
open AffineNine Matrix.GeneralLinearGroup.PrimeThreeFiveResidual

private theorem matrix_centralizer_test :
    ∀ B : Matrix (Fin 2) (Fin 2) (ZMod 3), B.det ≠ 0 →
      B * !![1, 1; 0, 1] = !![1, 1; 0, 1] * B →
      B * !![1, 0; 1, 1] = !![1, 0; 1, 1] * B →
      B = 1 ∨ B = -1 := by
  decide +kernel

private theorem centralizer_special (b : LinearGroup)
    (hc : ∀ s ∈ threeSpecialLinear, b * s = s * b) : b = 1 ∨ b = threeCentral := by
  let u : LinearGroup := mkOfDetNeZero !![1, 1; 0, 1] (by decide)
  let v : LinearGroup := mkOfDetNeZero !![1, 0; 1, 1] (by decide)
  have hu : u ∈ threeSpecialLinear := (three_mem_specialLinear u).mpr (by decide)
  have hv : v ∈ threeSpecialLinear := (three_mem_specialLinear v).mpr (by decide)
  rcases matrix_centralizer_test b.val b.det_ne_zero
    (congrArg Units.val (hc u hu)) (congrArg Units.val (hc v hv)) with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (h.trans (by decide : -(1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) = threeCentral.val)))

/-- Coordinates for the literal conjugation action, with its special linear
image and an actual element of A acting by inversion. -/
theorem exists_marked_action
    {X : Type*} [Group X] [Finite X] (P Y A : Subgroup X)
    [P.Normal] [IsElementaryAbelian 3 P] (hP : Nat.card P = 9)
    (hY : IsPPerfect 2 Y)
    (hcore : ¬ Y.pCoreIn 2 ≤ centralizer (P : Set X))
    (hYA : Y ≤ centralizer (A : Set X)) (hm : ⁅P, A⁆ ≠ ⊥) :
    ∃ (t : Translation →* X) (j : X →* LinearGroup), t.range = P ∧ Function.Injective t ∧
      (∀ g x, t (naturalAction (j g) x) = g * t x * g⁻¹) ∧
      (j.comp Y.subtype).range = threeSpecialLinear ∧
      ∃ a ∈ A, j a = threeCentral ∧ ∀ p : P, a * (p : X) * a⁻¹ = (p : X)⁻¹ := by
  obtain ⟨c, e, he⟩ := exists_plane_coordinates (p := 3) hP
  let α : X →* MulAut P := MulAut.conjNormal
  let j := e.toMonoidHom.comp α
  let f := j.comp Y.subtype
  have hfn : (pCore 2 Y).map f ≠ ⊥ := by
    intro hz
    apply hcore
    rintro _ ⟨y, hy, rfl⟩ p hp
    have hfy : f y = 1 := mem_bot.mp (hz ▸ mem_map_of_mem f hy)
    have hay : α y = 1 := e.injective (hfy.trans (map_one e).symm)
    have hh := congrArg (fun z : MulAut P => (z ⟨p, hp⟩ : X)) hay
    change (y : X) * p * (y : X)⁻¹ = p at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hSL : f.range = threeSpecialLinear := ternary_range_eq hY f hfn
  have hja : ∃ a ∈ A, j a ≠ 1 := by
    by_contra! hn
    apply hm
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro p hp a ha
    have hα : α a = 1 := e.injective ((hn a ha).trans (map_one e).symm)
    have hh := congrArg (fun z : MulAut P => (z ⟨p, hp⟩ : X)) hα
    change a * p * a⁻¹ = p at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨a, ha, han⟩ := hja
  have haj : j a = threeCentral := by
    refine (centralizer_special (j a) ?_).resolve_left han
    intro s hs
    obtain ⟨y, rfl⟩ := hSL ▸ hs
    change j a * j y = j y * j a
    rw [← map_mul, ← map_mul]
    exact congrArg j (hYA y.property a ha)
  let t : Translation →* X := P.subtype.comp c.symm.toMonoidHom
  refine ⟨t, j, ?_, P.subtype_injective.comp c.symm.injective, ?_, hSL, a, ha, haj, ?_⟩
  · change (P.subtype.comp c.symm.toMonoidHom).range = P
    rw [MonoidHom.range_comp, (MonoidHom.range_eq_top (f := c.symm.toMonoidHom)).mpr c.symm.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  · intro g x
    have hx := he (α g) (c.symm x)
    rw [c.apply_symm_apply] at hx
    have hh : naturalAction (j g) x = c (α g (c.symm x)) := hx
    change (c.symm (naturalAction (j g) x) : X) = _
    rw [hh, c.symm_apply_apply]
    rfl
  · intro p
    have hh : α a p = p⁻¹ := by
      apply c.injective
      rw [← he]
      change naturalAction (j a) (c p) = c p⁻¹
      rw [haj, map_inv]
      change Multiplicative.ofAdd (threeCentral.val *ᵥ (c p).toAdd) = (c p)⁻¹
      have hz : threeCentral.val = -(1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by decide
      rw [hz, Matrix.neg_mulVec, Matrix.one_mulVec]
      rfl
    exact congrArg Subtype.val hh

end Representation.NormalNineCentralInvolution
