module
public import Theory.SpecificGroups.PSL3Even.LargePlaneNormalizers.Planes
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Locals

/-!
# Large elementary actors and opposite locals in PSL₃

The local two-cores pull back along the actual projective UT₃ embedding to
the two coordinate planes. An elementary subgroup of order greater than |F|
lies in one plane and has that plane as its full PSL₃ centralizer. Its
intersection with the opposite core is contained in the highest-root group,
whose order is only |F|, so the actor escapes that core.

The ambient Chapter E adapter consumes this calculation and the separate
`LargeActorFixersAreInner` semilinear premise. The latter is an explicit
unproved input, not an assertion of automorphism centralizer control.
Source: Aschbacher–Smith, E.1.1–6 and E.1.14(1), printed pp.209–214,
and the plane geometry of §5.3.5–7, printed p.660.
-/

@[expose] public section
open scoped MatrixGroups
open Subgroup Matrix.PSL3 Matrix.PSL3.LinearThree
open Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3Even.TauGeometry
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The remaining semilinear calculation, stated on the actual projective
embedding. It is deliberately an explicit hypothesis of the ambient adapter. -/
def LargeActorFixersAreInner : Prop :=
  ∀ (A : Subgroup (U F)), (∀ a ∈ A, a^2 = 1) → Nat.card F < Nat.card A →
    ∀ (α : MulAut PSL(3,F)),
      (unipotent F).map α.toMonoidHom = unipotent F →
      (∃ k : ℕ, α^(2^k) = 1) →
      (∀ a ∈ A, α (projective F a) = projective F a) →
      α ∈ MulAut.innerSubgroup PSL(3,F)

/-- The intrinsic local cores pull back to exactly the two coordinate planes. -/
theorem core_comap_projective (b : Bool) :
    ((pCore 2 (localFactor F b)).map (localFactor F b).subtype).comap (projective F) =
      if b then V₁ F else V₂ F := by
  ext u
  cases b
  · change projective F u ∈ (pCore 2 (lineLocal F)).map (lineLocal F).subtype ↔ u ∈ V₂ F
    rw [lineLocal_twoCore_eq, lineRadical, Subgroup.map_map, mem_map, mem_V₂]
    let x : lineLocalSL F := ⟨specialLinear F u,
      (mem_lineLocalSL_iff F _).mpr ⟨rfl,rfl,rfl⟩⟩
    have he (y : lineLocalSL F) :
        ((lineLocal F).subtype.comp (lineLocalProjectEquiv F).toMonoidHom) y =
          projective F u ↔ y = x := by
      change projection F y.val = projection F x.val ↔ y = x
      constructor
      · intro h
        apply lineLocal_projection_injective F
        exact h
      · rintro rfl
        rfl
    simp only [he, exists_eq_right]
    rw [mem_lineRadicalSL_iff]
    change (1 = (1 : F) ∧ u.x = 0 ∧ (0 : F) = 0 ∧ (1 : F) = 1) ↔ u.x = 0
    simp only [true_and, and_true]
  · change projective F u ∈ (pCore 2 (pointLocal F)).map (pointLocal F).subtype ↔ u ∈ V₁ F
    rw [pointLocal_twoCore_eq, pointRadical, Subgroup.map_map, mem_map, mem_V₁]
    let x : pointLocalSL F := ⟨specialLinear F u,
      (mem_pointLocalSL_iff F _).mpr ⟨rfl,rfl,rfl⟩⟩
    have he (y : pointLocalSL F) :
        ((pointLocal F).subtype.comp (pointLocalProjectEquiv F).toMonoidHom) y =
          projective F u ↔ y = x := by
      change projection F y.val = projection F x.val ↔ y = x
      constructor
      · intro h
        apply pointLocal_projection_injective F
        exact h
      · rintro rfl
        rfl
    simp only [he, exists_eq_right]
    rw [mem_pointRadicalSL_iff]
    change ((1 : F) = 1 ∧ u.y = 0 ∧ (0 : F) = 0 ∧ (1 : F) = 1) ↔ u.y = 0
    simp only [true_and, and_true]

/-- A large elementary subgroup determines an inner centralizer plane and
escapes the core of the opposite local, including over the binary field. -/
theorem large_actor_opposite_local (A : Subgroup (U F))
    (he : ∀ a ∈ A, a^2 = 1) (hc : Nat.card F < Nat.card A) :
    ∃ b : Bool,
      centralizer (A.map (projective F) : Set PSL(3,F)) ≤ localFactor F b ∧
      ¬ A.map (projective F) ≤ (pCore 2 (localFactor F b)).map (localFactor F b).subtype := by
  have hp : ∃ b : Bool, A ≤ if b then V₁ F else V₂ F := by
    rcases le_plane_of_exponent_two F A he with h | h
    · exact ⟨true,h⟩
    · exact ⟨false,h⟩
  obtain ⟨b,hb⟩ := hp
  refine ⟨!b, ?_, ?_⟩
  · rw [LargePlaneNormalizers.centralizer_large_plane F A b hb hc]
    have hu : (if b then V₁ F else V₂ F).map (projective F) ≤ unipotent F := by
      rw [← projective_range]
      exact map_le_range _ _
    cases b
    · exact hu.trans (unipotent_le_pointLocal F)
    · exact hu.trans (unipotent_le_lineLocal F)
  · intro h
    have ho := map_le_iff_le_comap.mp h
    rw [core_comap_projective] at ho
    have hz : A ≤ Z F := by
      rw [← root_planes_inter]
      cases b
      · exact le_inf ho hb
      · exact le_inf hb ho
    have hcard := Subgroup.card_le_of_le hz
    rw [card_Z] at hcard
    exact (not_le_of_gt hc) hcard

end Matrix.PSL3Even.TauGeometry
