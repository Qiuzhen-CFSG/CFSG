module
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.Normalizer
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The source plane actor

This module constructs the literal two-residual of `L ∩ N(V₂)` and aligns
its permutation image with the even syntheme parabolic in the original A₆
coordinates. The actor is T-normalized and remains an actual subgroup of L.
Source: Aschbacher--Smith13.5.4 and13.5.6, printed pp.916–917.
-/
@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
open Section08.SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry NaturalPairing
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)

def planeLocal : Subgroup G := L ⊓ normalizer (V₂:Set G)
noncomputable def planeActor : Subgroup G :=
  (pResidual 2 (planeLocal (L:=L) (V₂:=V₂))).map (planeLocal (L:=L) (V₂:=V₂)).subtype

theorem planeLocal_preimage :
    (flagStabilizer (image d V₂)).comap (localMap d)=
      (normalizer (V₂:Set G)).subgroupOf L := by
  ext l
  constructor
  · intro hl
    have hh:=normalizes_plane_of_localMap_stabilizes d
      ((flagStabilizer (image d V₂)).comap (localMap d)) V₂
      (d.plane_le_seed.trans d.seed_le) (map_comap_le _ _)
    exact hh (mem_map_of_mem L.subtype hl)
  · intro hl
    change localMap d l∈flagStabilizer (image d V₂)
    apply (mem_stabilizer_iff_map _ _).mpr
    have hh:=QuadraticSource.image_conjugate_by_local d V₂
      (d.plane_le_seed.trans d.seed_le) (inclusion (QuadraticSource.L_le_local d) l)
    rw [←localMap_eq_full d l] at hh
    have he:V₂.map (MulAut.conj l.val).toMonoidHom=V₂:=mem_normalizer_iff_map_conj_eq.mp hl
    change image d (V₂.map (MulAut.conj l.val).toMonoidHom)=_ at hh
    rw [he] at hh
    exact hh.symm

theorem planeLocal_image :
    ((normalizer (V₂:Set G)).subgroupOf L).map (localMap d)=
      flagStabilizer (image d V₂) ⊓ alternatingGroup (Fin 6) := by
  rw [←planeLocal_preimage d,map_comap_eq,localMap_range d,inf_comm]

theorem planeLocal_image_marked : ∃a:alternatingGroup (Fin 6),
    ((normalizer (V₂:Set G)).subgroupOf L).map (localMap d)=
      L2.map (MulAut.conj a.val).toMonoidHom := by
  obtain ⟨a,_,ha⟩:=QuadraticSource.source_even_flag d
  refine ⟨a,?_⟩
  rw [planeLocal_image d,ha,flagStabilizer_move,flagStabilizer_plane]
  rw [L2,Subgroup.map_inf _ _ _ (MulAut.conj a.val).injective,conjugate_alternating]

omit [Finite G] in
theorem planeActor_le : planeActor (L:=L) (V₂:=V₂)≤planeLocal (L:=L) (V₂:=V₂) :=
  map_subtype_le _

theorem planeActor_twoPerfect : IsPPerfect 2 (planeActor (L:=L) (V₂:=V₂)) :=
  isPPerfect_embedded_pResidual 2 _

include d in
theorem planeActor_normalized : (T:Subgroup G)≤normalizer (planeActor (L:=L) (V₂:=V₂):Set G) := by
  exact ((le_inf d.normalizes_L (d.plane_stable.trans (normalizer (V₂:Set G)).le_normalizer)).trans inf_normalizer_le_normalizer_inf).trans
    (normalizer_le_normalizer_characteristic_image (planeLocal (L:=L) (V₂:=V₂)) (pResidual 2 _))

noncomputable def planeLocalMap : planeLocal (L:=L) (V₂:=V₂) →* Equiv.Perm (Fin 6) :=
  (localMap d).comp (inclusion inf_le_left)

theorem planeLocalMap_range : (planeLocalMap d).range=
    ((normalizer (V₂:Set G)).subgroupOf L).map (localMap d) := by
  ext g
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨⟨x.val,x.property.1⟩,x.property.2,rfl⟩
  · rintro ⟨l,hl,rfl⟩
    exact ⟨⟨l.val,l.property,hl⟩,rfl⟩

theorem planeActor_image : ∃a:alternatingGroup (Fin 6),
    (pResidual 2 (planeLocal (L:=L) (V₂:=V₂))).map (planeLocalMap d)=
      ((pResidual 2 L2).map L2.subtype).map (MulAut.conj a.val).toMonoidHom := by
  obtain ⟨a,ha⟩:=planeLocal_image_marked d
  refine ⟨a,?_⟩
  have hh:=map_embedded_pResidual 2 (⊤:Subgroup (planeLocal (L:=L) (V₂:=V₂))) (planeLocalMap d)
  rw [←MonoidHom.range_eq_map,planeLocalMap_range d,ha,←map_embedded_pResidual] at hh
  have ht:(pResidual 2 (⊤:Subgroup (planeLocal (L:=L) (V₂:=V₂)))).map (⊤:Subgroup (planeLocal (L:=L) (V₂:=V₂))).subtype=
      pResidual 2 (planeLocal (L:=L) (V₂:=V₂)):=map_pResidual_of_surjective 2 _ topEquiv.surjective
  rwa [ht] at hh

end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
