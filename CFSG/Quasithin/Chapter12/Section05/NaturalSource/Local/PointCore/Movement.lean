module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Quotients
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Geometry
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.PointResidual
public import Theory.GroupTheory.PCoreImage

/-!
# Movement and intrinsic core containment of the original point module

The residual actor is the restriction of the original quotient projection.
Its image is the actual two-space parabolic residual, whose exterior action
differences span V. Thus V = [V,L₁]. Since V lies in the marked Sylow and
normalizes L₁, it lies in L₁ and then in O₂(L₁). Relative normality of L₁
in G₁ transports this containment to O₂(G₁).

This proves the equal-component branch of source 12.5.8(1). It does not
assume or establish that L₁ is normal in G₁ in the other component branches.
Source: Aschbacher--Smith, 12.5.2(1) and 12.5.8(1), pp.817 and 820.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

theorem actorImage_Li (i : ℕ) (hi : LocalIndex i) :
    s.actorImage (s.marking.Li i) =
      Representation.SL5ExteriorSquare.parabolicResidual (localFlagDimension i) := by
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    have he : s.actor x = s.marking.componentActor ⟨x, s.marking.Li_le_L i hx⟩ :=
      s.actor_component ⟨x, s.marking.Li_le_L i hx⟩
    rw [he, ← s.marking.residualActor_apply i hi ⟨x, hx⟩]
    exact (s.marking.residualActor i hi ⟨x, hx⟩).property
  · intro g hg
    obtain ⟨l, hl⟩ := s.marking.residualActor_surjective i hi ⟨g, hg⟩
    refine ⟨⟨l, ((s.marking.Li_le_L i).trans le_sup_left) l.property⟩, l.property, ?_⟩
    have he := s.actor_component ⟨l, s.marking.Li_le_L i l.property⟩
    exact he.trans ((s.marking.residualActor_apply i hi l).symm.trans
      (congrArg Subtype.val hl))

theorem seed_point_commutator : ⁅V, s.marking.Li 1⁆ = V := by
  rw [← s.subspace_commutator ((s.marking.Li_le_L 1).trans le_sup_left),
    s.actorImage_Li 1 (Or.inl rfl)]
  change s.marking.subspace (Representation.BinaryOffender.subspaceCommutator
    (Representation.SL5TenDimensional.exteriorAction 2) ⊤
    (Representation.SL5ExteriorSquare.parabolicResidual 2)) = V
  rw [Representation.SL5ExteriorSquare.pointResidual_commutator_eq_top,
    s.marking.subspace_top]

theorem seed_le_point_residual : V ≤ s.marking.Li 1 := by
  calc
    V = ⁅V, s.marking.Li 1⁆ := s.seed_point_commutator.symm
    _ ≤ s.marking.Li 1 := le_normalizer_iff_commutator_le_right.mp
      (D.le_sylow.trans (s.sylow_normalizes_Li 1 (Or.inl rfl)))

theorem seed_le_point_residual_core : V ≤ (s.marking.Li 1).pCoreIn 2 := by
  let := D.elementary
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
    s.seed_le_point_residual ((s.marking.Li_le_L 1).trans D.normalizes)

theorem seed_le_point_core_of_normal
    (hn : ((s.marking.Li 1).subgroupOf (s.marking.Gi 1)).Normal) :
    V ≤ (s.marking.Gi 1).pCoreIn 2 :=
  s.seed_le_point_residual_core.trans
    (pCoreIn_mono_of_normalizes (s.marking.Li_le_Gi 1)
      ((normal_subgroupOf_iff_le_normalizer (s.marking.Li_le_Gi 1)).mp hn))

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
