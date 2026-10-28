module

public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Diagram
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Normalizers
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.BorelOvergroups
public import Theory.SpecificGroups.PSL3.BorelTwoParabolics
public import Theory.GroupTheory.SylowOvergroupIncidence

/-!
# Literal parabolic action over a fixed binary Sylow subgroup

Sylow conjugacy removes the inner-conjugacy ambiguity from the diagram
permutation: an automorphism preserving the standard Sylow subgroup sends each
of its two parabolics to the parabolic named by its diagram action. Consequently
an invariant proper subgroup containing the Borel is the Borel whenever one
actor exchanges the nodes.

Source: Aschbacher--Smith, E.2.2, printed pp.215--216, and E.2.7, p.219.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3.LinearThree.OuterExtensions
namespace Matrix.PSL3Even.MinimalParabolicWitness
variable (F : Type*) [Field F] [Finite F]
variable {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)

theorem borel_le_parabolic (b : Bool) : borel F ≤ parabolic F b := by
  cases b
  · exact (projective_parabolics_inf F).symm ▸ inf_le_right
  · exact (projective_parabolics_inf F).symm ▸ inf_le_left

theorem parabolic_ne_top (b : Bool) : parabolic F b ≠ ⊤ := by
  cases b
  · exact (projective_parabolics_isCoatom F).2.ne_top
  · exact (projective_parabolics_isCoatom F).1.ne_top

/-- The diagram action gives the literal image of a parabolic above a fixed Sylow. -/
theorem map_parabolic_of_preserves_unipotent (a : MulAut PSL(3,F))
    (ha : (unipotent F).map a.toMonoidHom = unipotent F) (b : Bool) :
    (parabolic F b).map a.toMonoidHom =
      parabolic F (diagramAction F hn hF a b) := by
  obtain ⟨g, hg⟩ := diagramAction_spec F hn hF a b
  rw [hg]
  apply (unipotentSylow F hn hF).conjugate_overgroup_eq_of_normalizer_le
  · exact (unipotent_le_borel F).trans (borel_le_parabolic F _)
  · change normalizer (unipotent F : Set PSL(3,F)) ≤ _
    rw [normalizer_unipotent F hn hF]
    exact (borel_le_parabolic F _).trans (parabolic F _).le_normalizer
  · rw [← hg, coe_unipotentSylow, ← ha]
    exact map_mono ((unipotent_le_borel F).trans (borel_le_parabolic F b))

/-- A proper invariant Borel overgroup cannot choose a node exchanged by an actor. -/
theorem eq_borel_of_swapping_actor (a : MulAut PSL(3,F))
    (ha : (unipotent F).map a.toMonoidHom = unipotent F)
    (hs : diagramAction F hn hF a ≠ 1) (D : Subgroup PSL(3,F))
    (hBD : borel F ≤ D) (hD : D ≠ ⊤) (hi : D.map a.toMonoidHom = D) :
    D = borel F := by
  have hswap (b : Bool) : diagramAction F hn hF a b = !b := by
    have hinj := (diagramAction F hn hF a).injective
    cases hp : diagramAction F hn hF a false <;>
      cases hq : diagramAction F hn hF a true
    · exact (Bool.false_ne_true (hinj (hp.trans hq.symm))).elim
    · have he : diagramAction F hn hF a = 1 := by ext b; cases b <;> assumption
      exact (hs he).elim
    · cases b <;> assumption
    · exact (Bool.false_ne_true (hinj (hp.trans hq.symm))).elim
  apply le_antisymm _ hBD
  rw [← projective_parabolics_inf]
  obtain h | h := BorelOvergroups.overgroup_borel F D hBD hD
  · have hm := map_mono (f := a.toMonoidHom) h
    rw [hi, show pointParabolic F = parabolic F true from rfl,
      map_parabolic_of_preserves_unipotent F hn hF a ha, hswap] at hm
    exact le_inf h hm
  · have hm := map_mono (f := a.toMonoidHom) h
    rw [hi, show lineParabolic F = parabolic F false from rfl,
      map_parabolic_of_preserves_unipotent F hn hF a ha, hswap] at hm
    exact le_inf hm h

end Matrix.PSL3Even.MinimalParabolicWitness
