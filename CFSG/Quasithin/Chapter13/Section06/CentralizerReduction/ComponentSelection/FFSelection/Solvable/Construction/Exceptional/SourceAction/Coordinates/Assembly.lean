module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Exceptional.SourceAction.Coordinates.Projections

/-!
# Simultaneous coordinates in the literal parity subgroup

The two even fibers coincide, so the permutation signs agree. The cubic
factor supplies every even three-point permutation: lift one through the
surjective cubic projection and remove its A₆ factor. After lifting the
six-point coordinate, this corrects the three-point coordinate without
changing the first. Disjoint kernels prove injectivity, giving one ambient
isomorphism carrying both original moved-space intertwiners.

Source: Aschbacher–Smith, B.5.7, printed p.106.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
universe u v
variable {G : Type u} [Group G]
variable (c : ChapterB.OuterSixThreeShape G)
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V) (d : Recovered c ρ)

include d in
/-- The two marked projections combine into the literal parity actor,
with both whole-group intertwiners carried by the same isomorphism. -/
theorem assemble_coordinates (s : SixCoordinates c ρ) (t : CubicCoordinates c ρ) :
    Nonempty (AmbientCoordinates c ρ) := by
  let : c.second.Normal := second_normal c
  have hpar (g : G) : Equiv.Perm.sign (s.projection g) = Equiv.Perm.sign (t.projection g) := by
    have hh : Equiv.Perm.sign (s.projection g) = 1 ↔ Equiv.Perm.sign (t.projection g) = 1 := by
      change g ∈ (alternatingGroup (Fin 6)).comap s.projection ↔
        g ∈ (alternatingGroup (Fin 3)).comap t.projection
      rw [s.even, t.even]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (s.projection g)) with h | h
    · rw [h, hh.mp h]
    · rcases Int.units_eq_one_or (Equiv.Perm.sign (t.projection g)) with h' | h'
      · exact ((by decide : (1 : ℤˣ) ≠ -1) ((hh.mpr h').symm.trans h)).elim
      · rw [h, h']
  have lift_even (r : Equiv.Perm (Fin 3)) (hr : r ∈ alternatingGroup (Fin 3)) :
      ∃ x ∈ c.second, t.projection x = r := by
    obtain ⟨g, rfl⟩ := t.surjective r
    have hg : g ∈ c.first ⊔ c.second := t.even ▸ hr
    obtain ⟨l, hl, x, hx, rfl⟩ := mem_sup_of_normal_right.mp hg
    have hl' : t.projection l = 1 := (show l ∈ t.projection.ker from t.kernel.symm ▸ hl)
    exact ⟨x, hx, by rw [map_mul, hl', one_mul]⟩
  let f : G →* SixPoint.Actor := {
    toFun g := ⟨(s.projection g, t.projection g), hpar g⟩
    map_one' := Subtype.ext (Prod.ext s.projection.map_one t.projection.map_one)
    map_mul' g h := Subtype.ext (Prod.ext (s.projection.map_mul g h) (t.projection.map_mul g h)) }
  have hf : Function.Bijective f := by
    constructor
    · apply (MonoidHom.ker_eq_bot_iff f).mp
      apply bot_unique
      intro g hg
      have hs : s.projection g = 1 := congrArg SixPoint.firstProjection hg
      have ht : t.projection g = 1 := congrArg SixPoint.secondProjection hg
      have hgS : g ∈ c.second := s.kernel ▸ hs
      have hgL : g ∈ c.first := t.kernel ▸ ht
      exact disjoint_def.mp d.supplement_disjoint
        ((le_sup_left : c.first ≤ c.first ⊔ d.offender) hgL) hgS
    · intro a
      obtain ⟨g, hg⟩ := s.surjective (SixPoint.firstProjection a)
      let r := (t.projection g)⁻¹ * SixPoint.secondProjection a
      have hr : r ∈ alternatingGroup (Fin 3) := by
        change Equiv.Perm.sign r = 1
        dsimp [r]
        rw [map_mul, map_inv, ← hpar g, hg, SixPoint.parity, inv_mul_cancel]
      obtain ⟨x, hx, htx⟩ := lift_even r hr
      have hsx : s.projection x = 1 := (show x ∈ s.projection.ker from s.kernel.symm ▸ hx)
      refine ⟨g * x, SixPoint.projections_injective _ _ ?_ ?_⟩
      · change s.projection (g * x) = SixPoint.firstProjection a
        rw [map_mul, hsx, mul_one, hg]
      · change t.projection (g * x) = SixPoint.secondProjection a
        rw [map_mul, htx]
        exact mul_inv_cancel_left _ _
  let e := MulEquiv.ofBijective f hf
  refine ⟨{ actorEquiv := e
            first_kernel := s.kernel
            second_kernel := t.kernel
            six_action := s.action
            cubic_action := t.action }⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
