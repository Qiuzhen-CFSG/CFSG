module
public import CFSG.Quasithin.ChapterG.Section11.FullLinearFourModel
/-!
# The marked full-four row and its canonical form

The whole-action intertwiner transports the original form. Full binary linear
invariance makes each pure summand isotropic; polarizing the mixed pairing and
using uniqueness of the invariant evaluation quadratic form identifies the
transported alternating form with the canonical natural-plus-dual pairing.
The new marked row retains the literal X and X₀ restrictions, point, space,
displacement and fixed-space clauses. Its consumer is exactly the exchanged
full GL₄(2) constituent quotient. Neither exhaustion nor ambient exclusion is
asserted, and the original thirteen-row `Conclusion` is unchanged.

Source: G.10.15--16, G.11.6--7 and the H.9 natural-plus-dual model; see the
full-four source correction in `docs/quasithin-proof-basis.md`.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open BinaryLinear.OuterCyclic BinaryNaturalDual.ModelOrbits
open scoped CharTwo
namespace CFSG.Quasithin.ChapterG.Section11.FullLinearFour.WholeActionModel
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {H : Subgroup G} {I J : Submodule (ZMod 2) V}
  (m : WholeActionModel ρ H I J)

theorem markedForm_eq_polar (B : LinearMap.BilinForm (ZMod 2) V)
    (halt : B.IsAlt) (hnd : B.Nondegenerate)
    (hp : ∀ g u w, B (ρ g u) (ρ g w) = B u w) :
    m.markedForm B = (BinaryNaturalDual.quadratic (V := Space 4)).polarBilin := by
  let A := AutomorphismModel.coordinateAction (Or.inl (rfl : 4 = 4))
  let C := m.markedForm B
  have hC := m.markedForm_preserves B hp
  have hCsym (u w : BinaryNaturalDual.CoordinateSpace 4) : C u w = C w u := by
    simpa only [CharTwo.neg_eq] using (m.markedForm_alternating B halt).neg_eq u w
  let N : Space 4 →ₗ[ZMod 2] BinaryNaturalDual.CoordinateSpace 4 := LinearMap.inl (ZMod 2) _ _
  let D : Module.Dual (ZMod 2) (Space 4) →ₗ[ZMod 2] BinaryNaturalDual.CoordinateSpace 4 := LinearMap.inr (ZMod 2) _ _
  have hN0 : C.compl₁₂ N N = 0 := by
    apply LinearMap.BilinForm.eq_zero_of_full_binary_linear_invariance
      (C.compl₁₂ N N) (fun u => m.markedForm_alternating B halt (N u)) _
      (by simp [Space])
    intro g u w
    change C (g u,0) (g w,0) = C (u,0) (w,0)
    have he := hC (MulAut.conj g) (u,0) (w,0)
    rw [A.on_inner,A.on_inner] at he
    simpa only [BinaryNaturalDual.naturalDualRepresentation_apply,map_zero] using he
  have hn (u w : Space 4) : C (u,0) (w,0) = 0 :=
    congrArg (fun F : LinearMap.BilinForm (ZMod 2) (Space 4) => F u w) hN0
  have hd (f k : Module.Dual (ZMod 2) (Space 4)) : C (0,f) (0,k) = 0 := by
    have he := hC (BinaryLinear.OuterCyclic.graphLinear 4)
      ((dotProductEquiv (ZMod 2) (Fin 4)).symm f,0)
      ((dotProductEquiv (ZMod 2) (Fin 4)).symm k,0)
    rw [A.on_graph,A.on_graph] at he
    simp only [BinaryNaturalDual.coordinateSwap_apply,map_zero,LinearEquiv.apply_symm_apply] at he
    exact he.trans (hn _ _)
  let P : BinaryNaturalDual.CoordinateSpace 4 →ₗ[ZMod 2] BinaryNaturalDual.CoordinateSpace 4 := N.comp (LinearMap.fst _ _ _)
  let R : BinaryNaturalDual.CoordinateSpace 4 →ₗ[ZMod 2] BinaryNaturalDual.CoordinateSpace 4 := D.comp (LinearMap.snd _ _ _)
  let Q := LinearMap.BilinMap.toQuadraticMap (C.compl₁₂ P R)
  have hQ (u : BinaryNaturalDual.CoordinateSpace 4) : Q u = C (u.1,0) (0,u.2) := rfl
  have hpolar : Q.polarBilin = C := by
    rw [LinearMap.BilinMap.polarBilin_toQuadraticMap]
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro w
    change C (u.1,0) (0,w.2) + C (w.1,0) (0,u.2) = C u w
    have hu : u = (u.1,0) + (0,u.2) := by simp
    have hw : w = (w.1,0) + (0,w.2) := by simp
    conv_rhs => rw [hu,hw]
    simp only [map_add,LinearMap.add_apply,hn,hd,zero_add,add_zero,
      hCsym (0,u.2) (w.1,0)]
    exact add_comm _ _
  have heq : Q = BinaryNaturalDual.quadratic := by
    apply quadratic_unique Q
    · intro u
      rw [hQ]
      exact map_zero _
    · intro f
      rw [hQ]
      exact congrArg (fun t : BinaryNaturalDual.CoordinateSpace 4 →ₗ[ZMod 2] ZMod 2 => t (0,f)) (map_zero C)
    · intro g u
      rw [hQ,hQ]
      have he := hC (MulAut.conj g) (u.1,0) (0,u.2)
      rw [A.on_inner,A.on_inner] at he
      simpa only [BinaryNaturalDual.naturalDualRepresentation_apply,map_zero] using he
    · rw [hpolar]
      exact m.markedForm_nondegenerate B hnd
  exact hpolar.symm.trans (congrArg QuadraticMap.polarBilin heq)

theorem form_coordinates (B : LinearMap.BilinForm (ZMod 2) V)
    (halt : B.IsAlt) (hnd : B.Nondegenerate)
    (hp : ∀ g u w, B (ρ g u) (ρ g w) = B u w) (u w : V) :
    B u w = (m.spaceEquiv u).2 (m.spaceEquiv w).1 +
      (m.spaceEquiv w).2 (m.spaceEquiv u).1 := by
  rw [← m.markedForm_apply B u w,m.markedForm_eq_polar B halt hnd hp,
    BinaryNaturalDual.polar_apply]

end CFSG.Quasithin.ChapterG.Section11.FullLinearFour.WholeActionModel

namespace CFSG.Quasithin.ChapterG.Section11.FullLinearFour
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {H : Subgroup G} {I J : Submodule (ZMod 2) V}

theorem WholeActionModel.marked_fixed_bound (m : WholeActionModel ρ H I J)
    (B : LinearMap.BilinForm (ZMod 2) V) (v : V) (X : Subgroup G) (X₀ : Subgroup X)
    (hb : ∀ x : X, x ∉ X₀ → ∀ u, ρ x u = u → B v u = 0) :
    ∀ x : m.actor X, x ∉ m.distinguishedActor X X₀ → ∀ u,
      (AutomorphismModel.coordinateAction (Or.inl rfl)).representation x u = u →
      m.markedForm B (m.markedPoint v) u = 0 := by
  intro x hx u hu
  obtain ⟨x,rfl⟩ := (m.actorEquiv X).surjective x
  obtain ⟨u,rfl⟩ := m.spaceEquiv.surjective u
  rw [m.actor_restriction] at hu
  rw [WholeActionModel.markedPoint,m.markedForm_apply]
  exact hb x (fun h => hx ((m.distinguishedActor_restriction X X₀ x).mpr h)) u
    (m.spaceEquiv.injective hu)

/-- The exceptional whole-action row, with the original marked data carried by
specified group and linear equivalences. This definition does not assert that
the old catalogue together with this row is exhaustive. -/
@[expose] def MarkedAlternative (ρ : Representation (ZMod 2) G V)
    (B : LinearMap.BilinForm (ZMod 2) V) (v : V) (W : Submodule (ZMod 2) V)
    (X : Subgroup G) (X₀ : Subgroup X) : Prop :=
  ∃ (H : Subgroup G) (I J : Submodule (ZMod 2) V) (m : WholeActionModel ρ H I J),
    m.markedForm B = (BinaryNaturalDual.quadratic (V := Space 4)).polarBilin ∧
    m.markedPoint v ≠ 0 ∧ m.markedPoint v ∈ m.markedSpace W ∧
    IsElementaryAbelian 2 (m.actor X) ∧
    (∀ x : m.actor X, (AutomorphismModel.coordinateAction (Or.inl rfl)).representation x
      (m.markedPoint v) = m.markedPoint v) ∧
    (∀ u ∈ m.markedSpace W, ∀ w ∈ m.markedSpace W, m.markedForm B u w = 0) ∧
    (∀ x : m.actor X, ∀ u, m.markedForm B (m.markedPoint v) u = 0 →
      (AutomorphismModel.coordinateAction (Or.inl rfl)).representation x u - u ∈ m.markedSpace W) ∧
    (∀ x : m.actor X, x ∉ m.distinguishedActor X X₀ → ∀ u,
      (AutomorphismModel.coordinateAction (Or.inl rfl)).representation x u = u →
      m.markedForm B (m.markedPoint v) u = 0)

/-- A separately named corrected target; the original thirteen-row public
`Conclusion` remains unchanged. Exhaustion is a separate classification theorem. -/
@[expose] def ConclusionWithFullLinearFour (ρ : Representation (ZMod 2) G V)
    (B : LinearMap.BilinForm (ZMod 2) V) (v : V) (W : Submodule (ZMod 2) V)
    (X : Subgroup G) (X₀ : Subgroup X) : Prop :=
  Conclusion ρ B X ∨ MarkedAlternative ρ B v W X X₀

variable [Finite G] [FiniteDimensional (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V} {v : V} {W : Submodule (ZMod 2) V}
  {X : Subgroup G} [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

/-- The literal full-four exchanged constituent yields the new whole-action
row, including the canonical form and restrictions of the original X and X₀. -/
theorem exchanged_full_four_marked_alternative
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X) (hn : ¬ Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L) (hm : ⁅L,X⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) V} (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I)
    (hgeo : Section10.ExchangedConstituentGeometry ρ B v W X I)
    (hfour : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ (componentOrbit L ⊤)
        (X ⊓ subspaceStabilizer ρ I) I hI.invariant inf_le_right)) ⊤ ⊤
      (Section06.binaryLinearAction 4)) : MarkedAlternative ρ B v W X X₀ := by
  obtain ⟨x,⟨m⟩⟩ := exchanged_full_four_model h cover hw hS hn hL hm hI hgeo hfour
  refine ⟨componentOrbit L ⊤,I,I.map (ρ x),m,
    m.markedForm_eq_polar B h.alternating h.nondegenerate h.preserves,?_,?_,
    m.actor_elementary X,m.marked_point_fixed v X h.fixes_point,
    m.marked_space_isotropic B W h.isotropic,m.marked_displacement B v W X h.displacement,
    m.marked_fixed_bound B v X X₀ h.fixed_bound⟩
  · exact fun hz => h.point_ne_zero (m.spaceEquiv.map_eq_zero_iff.mp hz)
  · exact Submodule.mem_map_of_mem h.point_mem

end CFSG.Quasithin.ChapterG.Section11.FullLinearFour
