module
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.ElementarySubgroups
/-!
# Self-centralization of the planes in the full root normalizer

Commuting with a noncentral axis point eliminates the graph–field coset
and one diagonal scalar. Commuting with a central point eliminates the
remaining scalar. The root-coordinate commutator then places the element
inside the plane. This calculates the action kernel in the actual split
normalizer, not merely inside its root subgroup.

Source: Aschbacher, *Sporadic Groups* (1994), 46.14(3,5a), pp.257–258.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Four.RootNormalizerModel
open Cubic Theory.GroupTheory.HyperbolicRecognition

/-- The full split normalizer centralizes the first plane only through the plane itself. -/
theorem centralizes_first_plane (g : Model)
    (hc : ∀ q ∈ rootPlane₁, g * SemidirectProduct.inl q = SemidirectProduct.inl q * g) :
    g.right = 1 ∧ g.left ∈ rootPlane₁ := by
  have haxis : g ∈ centralizer ({uHom (Multiplicative.ofAdd (1 : F))} : Set Model) :=
    mem_centralizer_singleton_iff.mpr (hc ⟨1,0,0⟩ (by simp))
  obtain ⟨hy,b,hb⟩ := (centralizes_axis_iff 1 one_ne_zero g).mp haxis
  have hz := (commute_inl_iff g ⟨0,0,1⟩).mp (hc ⟨0,0,1⟩ (by simp))
  rw [hb] at hz
  have hbc : (b : F) = 1 := by
    have hh := congrArg SylowModel.U.c hz
    have hh' : g.left.c + (b : F) = 1 + g.left.c := by
      simpa [torus,diagonalHom,diagonal] using hh
    exact add_left_cancel (hh'.trans (add_comm _ _))
  have hb1 : b = 1 := Units.ext hbc
  refine ⟨?_,(mem_rootPlane₁ g.left).mpr hy⟩
  rw [hb,hb1]
  exact map_one torus

/-- The second root plane is likewise self-centralizing in the full split normalizer. -/
theorem centralizes_second_plane (g : Model)
    (hc : ∀ q ∈ rootPlane₂, g * SemidirectProduct.inl q = SemidirectProduct.inl q * g) :
    g.right = 1 ∧ g.left ∈ rootPlane₂ := by
  have haxis := (commute_inl_iff g ⟨0,1,0⟩).mp (hc ⟨0,1,0⟩ (by simp))
  have hz := (commute_inl_iff g ⟨0,0,1⟩).mp (hc ⟨0,0,1⟩ (by simp))
  obtain ⟨a,ha | ha⟩ := actor_normal_form g.right
  · rw [ha] at haxis hz
    have hb : (a.2 : F) = 1 := by
      have hh := congrArg SylowModel.U.y haxis
      have hh' : g.left.y + (a.2 : F) = 1 + g.left.y := by
        simpa [diagonalHom,diagonal] using hh
      exact add_left_cancel (hh'.trans (add_comm _ _))
    have ha1 : (a.1 : F) = 1 := by
      have hh := congrArg SylowModel.U.c hz
      have hh' : g.left.c + (a.1 : F) = 1 + g.left.c := by
        simpa [diagonalHom,diagonal,hb] using hh
      exact add_left_cancel (hh'.trans (add_comm _ _))
    have hx : g.left.x = 0 := by
      have hh := congrArg SylowModel.U.c haxis
      simpa [diagonalHom,diagonal,hb] using hh
    refine ⟨?_,(mem_rootPlane₂ g.left).mpr hx⟩
    apply Subtype.ext
    rw [ha,show a = 1 from Prod.ext (Units.ext ha1) (Units.ext hb),map_one]
    rfl
  · rw [ha] at haxis
    have hh := congrArg SylowModel.U.y haxis
    simp [diagonalHom,diagonal,graphField,graph,SylowModel.frob] at hh
end Matrix.PSL3Four.RootNormalizerModel
