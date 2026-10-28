module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity.Module
public import Theory.SpecificGroups.PSL3Two.Parabolics.Actions
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals

/-!
# The actual point-radical image in the local collapse

The original natural coordinates send the marked involution z to a nonzero
binary vector. The source identity N_G(V₁) = C_G(z) identifies the image of
L ∩ N_G(V₁) with its vector stabilizer. Transitivity on the seven nonzero
vectors identifies this stabilizer with a conjugate of the standard point
parabolic.

Images preserve the two-residual, and the two-group kernel of the unchanged
qL also preserves the embedded two-core. Thus the literal map from O₂(L₁)
has image g O₂(O²(P₁)) g⁻¹, the point radical. The residual is used to
identify L₁; the final acting subgroup is its TWO-CORE.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Notation 12.8.2 and Lemma 14.7.74, printed pp.849 and 1077 (PDF p.1094).
-/

@[expose] public section

open Subgroup Representation Matrix.PSL3Two
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity.Displacement
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

private def seedPoint : V := ⟨d.z, F.le_seed 1 (d.point ▸ mem_zpowers d.z)⟩
private noncomputable def markedPoint : Fano.Point :=
  ⟨(d.naturalCoordinates (seedPoint d)).toAdd, by
    intro h
    have he : d.naturalCoordinates (seedPoint d) = d.naturalCoordinates 1 := by
      rw [map_one]
      exact h
    exact d.z_ne_one (congrArg Subtype.val (d.naturalCoordinates_bijective.1 he))⟩

private theorem source_point_stabilizer (l : L) :
    (l : G) ∈ F.Gi 1 ↔ d.qL l ∈ MulAction.stabilizer SL (markedPoint d) := by
  have he := d.naturalCoordinates_equivariant l (seedPoint d)
  rw [show F.Gi 1 = F.H from rfl, d.centralizer_eq, mem_centralizer_singleton_iff]
  change _ ↔ d.qL l • markedPoint d = markedPoint d
  constructor
  · intro h
    apply Subtype.ext
    change BinaryLinearThree.W (d.qL l) (markedPoint d).val = (markedPoint d).val
    change BinaryLinearThree.W (d.qL l) (d.naturalCoordinates (seedPoint d)).toAdd = _
    rw [← he]
    congr 2
    apply Subtype.ext
    change (l : G) * d.z * (l : G)⁻¹ = d.z
    rw [h, mul_inv_cancel_right]
  · intro h
    have hh := he.trans (congrArg Subtype.val h)
    have hh' := d.naturalCoordinates_bijective.1 hh
    have hc := congrArg Subtype.val hh'
    exact mul_inv_eq_iff_eq_mul.mp hc

private theorem source_parabolic_image :
    ((F.Gi 1).subgroupOf L).map d.qL = MulAction.stabilizer SL (markedPoint d) := by
  ext g
  constructor
  · rintro ⟨l,hl,rfl⟩
    exact (source_point_stabilizer d l).mp hl
  · intro hg
    obtain ⟨l,rfl⟩ := d.qL_surjective g
    exact ⟨l,(source_point_stabilizer d l).mpr hg,rfl⟩

private theorem Li_subgroupOf :
    (F.Li L 1).subgroupOf L =
      (pResidual 2 ((F.Gi 1).subgroupOf L)).map ((F.Gi 1).subgroupOf L).subtype := by
  apply Subgroup.map_injective L.subtype_injective
  rw [map_subgroupOf_eq_of_le ((F.Li_le L 1).trans inf_le_left),
    map_embedded_pResidual, subgroupOf_map_subtype, inf_comm]
  simp only [InvariantFlag.Li, show ¬(3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide, ↓reduceIte]

private theorem parabolicMap_range :
    (parabolicMap d).range =
      ((MarkedAutomorphisms.residual (MulAction.stabilizer SL (markedPoint d))).pCoreIn 2) := by
  have hker : IsPGroup 2 d.qL.ker := by
    rw [d.qL_ker]
    exact (isPGroup_pCoreIn 2 L).comap_subtype
  have hcore : ((F.Li L 1).pCoreIn 2).subgroupOf L =
      ((F.Li L 1).subgroupOf L).pCoreIn 2 := by
    apply Subgroup.map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans
      ((F.Li_le L 1).trans inf_le_left)), map_pCoreIn_of_injective 2 _ _ L.subtype_injective,
      map_subgroupOf_eq_of_le ((F.Li_le L 1).trans inf_le_left)]
  have hr : (parabolicMap d).range =
      (((F.Li L 1).pCoreIn 2).subgroupOf L).map d.qL := by
    ext x
    constructor
    · rintro ⟨p,rfl⟩
      exact ⟨_,p.property,rfl⟩
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,hl⟩,rfl⟩
  rw [hr, hcore, map_pCoreIn_of_ker_isPGroup d.qL hker, Li_subgroupOf,
    map_embedded_pResidual, source_parabolic_image]
  rfl

/-- Under the original quotient marking, the actor is a conjugate of the point radical. -/
theorem exists_parabolicMap_range : ∃ g : SL,
    (parabolicMap d).range = MarkedAutomorphisms.pointV.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL flagPoint (markedPoint d)
  obtain ⟨g,rfl⟩ := project_surjective g
  rw [Fano.project_smul_point] at hg
  refine ⟨g,?_⟩
  rw [parabolicMap_range, ← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    Fano.stabilizer_flagPoint_SL]
  unfold MarkedAutomorphisms.residual
  rw [← map_embedded_pResidual]
  rw [← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
  rw [show (pResidual 2 pointParabolicSL).map pointParabolicSL.subtype = MarkedAutomorphisms.pointA from MarkedAutomorphisms.point_residual,
    MarkedAutomorphisms.point_core]
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.NaturalRigidity.Displacement
