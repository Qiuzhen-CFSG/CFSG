module
public import Theory.SpecificGroups.PSL3Even.MinimalParabolicWitness.Center
public import Theory.Mathieu.M23.Properties.ElementarySylowNormal
/-!
# A marked PSL3(4) Sylow cannot acquire a graph actor in M23

Every order-sixteen elementary subgroup of an M23 Sylow subgroup is fixed
by that Sylow. An embedded root plane is consequently invariant under each
literal conjugating actor. Its parabolic normalizer has the same type, so
the induced PSL3(4) diagram permutation is trivial. The second theorem needs
only the binary unipotent embedding, allowing odd central covering layers.

Source: Aschbacher--Smith 14.2.9, printed p.983, repairing the marked M23
exception without imposing subgroup movement on the original normal K.
-/
public section
open scoped MatrixGroups
open Subgroup Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3Even.UnipotentGeometry
open Matrix.PSL3Even.AutomorphismCoverage.RootOrientation
namespace Sporadic.Mathieu
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The actual embedded Sylow root plane cannot have a graph-swapping actor
inside a Sylow subgroup of M23. -/
theorem m23_no_marked_linear_three_four_graph
    (hF : Nat.card F = 4) (i : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F →* M23)
    (hi : Function.Injective i) (P : Sylow 2 M23)
    (hP : (unipotent F).map i ≤ (P : Subgroup M23))
    (t : M23) (ht : t ∈ (P : Subgroup M23))
    (a : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))
    (_ha : (unipotent F).map a.toMonoidHom = unipotent F)
    (hact : ∀ x, i (a x) = t * i x * t⁻¹) :
    diagramAction F (n := 2) (by decide) hF a = 1 := by
  let V := rootPlane F true
  have he : V = (V₁ F).map (projective F) := rootPlane_eq_map F true
  have hVe : IsElementaryAbelian 2 V := by rw [he]; exact IsElementaryAbelian.map _
  have hVc : Nat.card V = 16 := by rw [he,card_map_of_injective (projective_injective F),card_V₁,hF]; norm_num
  have hVu : V ≤ unipotent F := map_mono (rootPlaneSL_le_unipotent F true)
  have hN := M23Geometry.ElementarySylow.card16_normalized_in_sylow P (V.map i)
    (by let := hVe; exact IsElementaryAbelian.map _)
    ((card_map_of_injective hi).trans hVc) ((map_mono hVu).trans hP)
  have hfix : V.map a.toMonoidHom = V := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      have hn := (mem_normalizer_iff.mp (hN ht) (i x)).mp (mem_map_of_mem i hx)
      rw [←hact] at hn
      obtain ⟨y,hy,hyx⟩ := hn
      exact hi hyx ▸ hy
    · rw [card_map_of_injective a.injective]
  apply diagramAction_linearField F (n := 2) (by decide) hF
  apply (mapsParabolicType_self_iff_mem_linearField F (n := 2) (by decide) hF a true).mp
  refine ⟨1,?_⟩
  rw [←normalizer_rootPlane F true,map_equiv_normalizer_eq,hfix,map_one]
  change _ = (normalizer (rootPlane F true : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))).map (MonoidHom.id _)
  rw [map_id]
/-- Only the actual binary Sylow embedding is needed; odd central covering
layers of the component do not impose an embedding of the whole PSL quotient. -/
theorem m23_no_marked_unipotent_four_graph
    (hF : Nat.card F = 4) (i : U F →* M23) (hi : Function.Injective i)
    (P : Sylow 2 M23) (hP : i.range ≤ (P : Subgroup M23))
    (t : M23) (ht : t ∈ (P : Subgroup M23))
    (a : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))
    (α : MulAut (U F)) (hproj : ∀ x, projective F (α x) = a (projective F x))
    (hact : ∀ x, i (α x) = t * i x * t⁻¹) :
    diagramAction F (n := 2) (by decide) hF a = 1 := by
  have hVc : Nat.card (V₁ F) = 16 := by rw [card_V₁,hF]; norm_num
  have hN := M23Geometry.ElementarySylow.card16_normalized_in_sylow P ((V₁ F).map i)
    (IsElementaryAbelian.map i) ((card_map_of_injective hi).trans hVc)
    ((map_le_range _ _).trans hP)
  have hfix : (V₁ F).map α.toMonoidHom = V₁ F := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      have hn := (mem_normalizer_iff.mp (hN ht) (i x)).mp (mem_map_of_mem i hx)
      rw [←hact] at hn
      obtain ⟨y,hy,hyx⟩ := hn
      exact hi hyx ▸ hy
    · rw [card_map_of_injective α.injective]
  have hroot : (rootPlane F true).map a.toMonoidHom = rootPlane F true := by
    rw [rootPlane_eq_map, if_pos rfl, map_map]
    have hp : a.toMonoidHom.comp (projective F) =
        (projective F).comp α.toMonoidHom := by ext x; exact (hproj x).symm
    rw [hp, ←map_map, hfix]
  apply diagramAction_linearField F (n := 2) (by decide) hF
  apply (mapsParabolicType_self_iff_mem_linearField F (n := 2) (by decide) hF a true).mp
  refine ⟨1,?_⟩
  rw [←normalizer_rootPlane F true,map_equiv_normalizer_eq,hroot,map_one]
  change _ = (normalizer (rootPlane F true : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))).map (MonoidHom.id _)
  rw [map_id]
end Sporadic.Mathieu
