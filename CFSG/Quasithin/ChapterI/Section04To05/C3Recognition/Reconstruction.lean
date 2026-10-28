module

public import CFSG.Quasithin.ChapterI.Section04To05.Geometry
public import Theory.LinearAlgebra.BinaryPolarGeometry.Action
public import Theory.Representation.BinaryPolarity.SymplecticAction
public import Theory.SpecificGroups.SymplecticSix.Basic

/-!
# The marked six-space in C₃ recognition

The points are the actual cosets of the original vertex group. Earlier
I.5.8–14 supply their cardinality, faithful action, and the one-or-all triples
on singular and nonsingular lines. Their non-incidence row span is a binary
symplectic six-space. A symplectic basis gives a faithful homomorphism into
the literal Sp₆(2), retaining the point map, collinearity and stabilizers.

The `GeometryData` fields are explicitly earlier geometric conclusions.
They do not assume a linear representation, form, or recognition theorem.
Their construction from a bare D-system is a separate source obligation.

Source: Aschbacher–Smith I.5.15, combined manuscript, printed p.424.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.C3Recognition
open Matrix
open Theory.LinearAlgebra
open Theory.SpecificGroups.SymplecticSix
variable {G : Type*} [Group G] (S : DSystem .C3 G)

/-- Precisely the earlier point geometry used in I.5.15. -/
structure GeometryData : Prop where
  card_points : Nat.card S.Point = 63
  faithful_points : FaithfulSMul G S.Point
  noncollinear : ∀ x : S.Point, ∃ y, ¬ S.Collinear x y
  triples : ∀ x y : S.Point, x ≠ y →
    ∃ z, BinaryPolarGeometry.OneOrAll S.Collinear x y z

namespace GeometryData
variable {S} (d : GeometryData S)

include d in
theorem finite_points : Finite S.Point :=
  Nat.finite_of_card_ne_zero (by rw [d.card_points]; decide)

include d in
theorem polarData : BinaryPolarGeometry.Data S.Collinear := {
  reflexive := S.collinear_refl
  symmetric := S.collinear_symm
  nonincident := d.noncollinear
  triples := d.triples }

end GeometryData

theorem collinear_action (g : G) (x y : S.Point) :
    S.Collinear (g • x) (g • y) ↔ S.Collinear x y := by
  constructor
  · intro h
    simpa only [inv_smul_smul] using h.smul S g⁻¹
  · exact fun h => h.smul S g

/-- A marking by the actual standard symplectic space, with the original action. -/
structure SymplecticMark where
  point : S.Point → Vector (ZMod 2)
  point_nonzero : ∀ x, point x ≠ 0
  point_bijective : Function.Bijective (fun x => (⟨point x, point_nonzero x⟩ :
    {v : Vector (ZMod 2) // v ≠ 0}))
  hom : G →* Sp (ZMod 2)
  hom_injective : Function.Injective hom
  equivariant : ∀ g x, (hom g).val *ᵥ point x = point (g • x)
  orthogonal : ∀ x y, form (ZMod 2) (point x) (point y) = 0 ↔ S.Collinear x y

namespace SymplecticMark
variable {S} (m : SymplecticMark S)

theorem point_injective : Function.Injective m.point := by
  intro x y h
  exact m.point_bijective.injective (Subtype.ext h)

theorem fixes_basePoint_iff (g : G) :
    (m.hom g).val *ᵥ m.point S.basePoint = m.point S.basePoint ↔ g ∈ S.family 0 := by
  rw [m.equivariant, m.point_injective.eq_iff]
  change g ∈ MulAction.stabilizer G S.basePoint ↔ _
  rw [S.stabilizer_basePoint]

end SymplecticMark

theorem exists_symplecticMark (d : GeometryData S) : Nonempty (SymplecticMark S) := by
  let : Finite S.Point := d.finite_points
  let : FaithfulSMul G S.Point := d.faithful_points
  let V := BinaryPolarGeometry.Space S.Collinear
  let p := BinaryPolarGeometry.point S.Collinear
  let b := d.polarData
  let ρ := BinaryPolarGeometry.Data.representation (collinear_action S)
  have hd : Module.finrank (ZMod 2) V = 2 * 3 :=
    b.space_finrank 6 (by rw [d.card_points]; decide)
  obtain ⟨e, φ, hφ, he⟩ := BinaryPolarity.exists_marked_symplectic_action 3 ρ
    (b.representation_injective (collinear_action S)) hd b.form b.form_alternating
    b.form_nondegenerate (b.form_invariant (collinear_action S))
  let q : S.Point → Vector (ZMod 2) := fun x => e (p x)
  have hq (x : S.Point) : q x ≠ 0 :=
    fun h => b.point_nonzero x (e.toLinearEquiv.map_eq_zero_iff.mp h)
  refine ⟨⟨q, hq, ?_, φ, hφ, ?_, ?_⟩⟩
  · constructor
    · intro x y h
      exact b.point_injective (e.toLinearEquiv.injective (congrArg Subtype.val h))
    · intro v
      obtain ⟨x, hx⟩ := b.pointEquiv.surjective
        ⟨e.symm v.val, fun h => v.property (by
          have he' := congrArg e h
          exact (e.toLinearEquiv.apply_symm_apply v.val).symm.trans
            (he'.trans (map_zero e)) )⟩
      refine ⟨x, Subtype.ext ?_⟩
      change e (p x) = v.val
      rw [show p x = e.symm v.val from congrArg Subtype.val hx]
      exact e.toLinearEquiv.apply_symm_apply v.val
  · intro g x
    change (φ g).val *ᵥ e (p x) = e (p (g • x))
    rw [he, BinaryPolarGeometry.Data.representation_point]
  · intro x y
    change Matrix.PSp4Three.form (e (p x)) (e (p y)) = 0 ↔ _
    rw [e.map_app]
    exact b.orthogonal_iff x y

end Quasithin.I5.C3Recognition
