module

public import Theory.SpecificGroups.PSL3Even.MinimalParabolicWitness.Diagram
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage.RootOrientation.Planes

/-!
# Elementary subgroups fixed by a diagram-swapping Sylow actor

In binary UT₃ every elementary subgroup lies in one of its two root planes.
A Sylow-preserving actor permutes those planes exactly as it permutes their
parabolic normalizers. If it exchanges the nodes and fixes the elementary
subgroup, that subgroup lies in both planes, hence in the highest root.

Source: Aschbacher--Smith, E.2.7, printed p.219.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3Even.UnipotentGeometry
open Matrix.PSL3Even.AutomorphismCoverage.RootOrientation
namespace Matrix.PSL3Even.MinimalParabolicWitness
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)

theorem map_rootPlane_of_preserves_unipotent (a : MulAut PSL(3,F))
    (ha : (unipotent F).map a.toMonoidHom = unipotent F) (b : Bool) :
    (rootPlane F b).map a.toMonoidHom =
      rootPlane F (diagramAction F hn hF a b) := by
  obtain ⟨c,hc₁,hc₂⟩ := upper_plane_permutation F a ha
  obtain ⟨d,hd⟩ : ∃ d, (rootPlane F b).map a.toMonoidHom = rootPlane F d := by
    cases b
    · exact ⟨!c,hc₂⟩
    · exact ⟨c,hc₁⟩
  have hp : (parabolic F b).map a.toMonoidHom = parabolic F d := by
    rw [← normalizer_rootPlane F b, Subgroup.map_equiv_normalizer_eq, hd,
      normalizer_rootPlane]
  have he : diagramAction F hn hF a b = d := by
    apply (diagramAction_apply_iff F hn hF a b d).mpr
    refine ⟨1, ?_⟩
    rw [map_one]
    change _ = (parabolic F d).map (MonoidHom.id _)
    rwa [Subgroup.map_id]
  rw [he]
  exact hd

private theorem bool_swap (π : Equiv.Perm Bool) (hπ : π ≠ 1) (b : Bool) : π b = !b := by
  have hinj := π.injective
  cases hp : π false <;> cases hq : π true
  · exact (Bool.false_ne_true (hinj (hp.trans hq.symm))).elim
  · have he : π = 1 := by ext b; cases b <;> assumption
    exact (hπ he).elim
  · cases b <;> assumption
  · exact (Bool.false_ne_true (hinj (hp.trans hq.symm))).elim

/-- The elementary subgroup is the supplied one, not a maximal replacement. -/
theorem elementary_invariant_le_center (a : MulAut PSL(3,F))
    (ha : (unipotent F).map a.toMonoidHom = unipotent F)
    (hs : diagramAction F hn hF a ≠ 1) (A : Subgroup PSL(3,F))
    [IsElementaryAbelian 2 A] (hA : A ≤ unipotent F)
    (hi : A.map a.toMonoidHom = A) : A ≤ projectiveCenter F := by
  let W := A.comap (projective F)
  have hW : W.map (projective F) = A := by
    apply map_comap_eq_self
    rw [projective_range]
    exact hA
  have hexp (u : U F) (hu : u ∈ W) : u ^ 2 = 1 := by
    apply projective_injective F
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (projective F u) hu
  obtain ⟨b,hb⟩ : ∃ b : Bool, A ≤ rootPlane F b := by
    obtain h | h := le_plane_of_exponent_two F W hexp
    · refine ⟨true, ?_⟩
      rw [rootPlane_eq_map, ← hW]
      exact map_mono h
    · refine ⟨false, ?_⟩
      rw [rootPlane_eq_map, ← hW]
      exact map_mono h
  have ho : A ≤ rootPlane F (!b) := by
    have hm := map_mono (f := a.toMonoidHom) hb
    rw [hi, map_rootPlane_of_preserves_unipotent F hn hF a ha, bool_swap _ hs] at hm
    exact hm
  have hiZ : rootPlane F true ⊓ rootPlane F false = projectiveCenter F := by
    rw [rootPlane_eq_map, rootPlane_eq_map]
    change (V₁ F).map (projective F) ⊓ (V₂ F).map (projective F) = _
    rw [← Subgroup.map_inf _ _ _ (projective_injective F), root_planes_inter]
    rfl
  rw [← hiZ]
  cases b
  · exact le_inf ho hb
  · exact le_inf hb ho

end Matrix.PSL3Even.MinimalParabolicWitness
