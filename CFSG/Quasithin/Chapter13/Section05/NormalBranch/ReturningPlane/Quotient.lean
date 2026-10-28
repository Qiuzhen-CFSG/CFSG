module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.TypeU4
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.Marking
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.Quotient
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.ReturningPlane.PointCores

/-!
# The original quaternion-core image in the natural A₆ quotient

Equivariance identifies the image of each relative module normalizer with
its actual alternating stabilizer. Since L₁ is the two-residual of the
source point centralizer, its two-core lies in that point stabilizer's
two-core. The13.5.15 identity U_H=O₂(L₁) therefore places the original
U_H image in the marked four-group. No returning-intersection identity
or conjugate placement is an assumption.

Source: Aschbacher–Smith,13.5.15(5) and13.5.16, printed pp.920–921,
with the preceding natural setup of13.2.1 and13.3.3 retained explicitly.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane
open Section08.SourceCompletion
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
open PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {V₂ M : Subgroup G} {g : G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

include d

theorem localNormalizer_mem (X : Subgroup G) (hX : X ≤ D.V) (l : D.L) :
    l.val ∈ normalizer (X : Set G) ↔
      localMap d l ∈ flagStabilizer (Section07.NaturalAction.image d X) := by
  let lM := inclusion (QuadraticSource.L_le_local d) l
  have he := QuadraticSource.image_conjugate_by_local d X hX lM
  have hq : QuadraticSource.permutation d lM = localMap d l :=
    (QuadraticSource.local_permutation_extension d).choose_spec.1 l
  rw [hq] at he
  rw [mem_stabilizer_iff_map]
  constructor
  · intro hn
    change move (localMap d l) (Section07.NaturalAction.image d X) = _
    rw [← he]
    exact congrArg (Section07.NaturalAction.image d) (mem_normalizer_iff_map_conj_eq.mp hn)
  · intro hn
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply QuadraticSource.image_injective_on_subgroups d ?_ hX (he.trans hn)
    rintro _ ⟨x, hx, rfl⟩
    exact mem_normalizer_iff.mp (d.normalizes_V (mem_sup_left l.property)) x |>.mp (hX hx)

/-- The quotient image is the literal A₆ stabilizer of the marked source subspace. -/
theorem localNormalizer_image (X : Subgroup G) (hX : X ≤ D.V) :
    ((D.L ⊓ normalizer (X : Set G)).subgroupOf D.L).map (localMap d) =
      alternatingGroup (Fin 6) ⊓ flagStabilizer (Section07.NaturalAction.image d X) := by
  apply le_antisymm
  · rintro a ⟨l, hl, rfl⟩
    exact ⟨(localMap_range d) ▸ (show localMap d l ∈ (localMap d).range from ⟨l,rfl⟩),
      (localNormalizer_mem d X hX l).mp hl.2⟩
  · intro a ha
    obtain ⟨l, hl⟩ := (localMap_range d).symm ▸ ha.1
    refine ⟨l, ⟨l.property, (localNormalizer_mem d X hX l).mpr ?_⟩, hl⟩
    rw [hl]
    exact ha.2

/-- The original quaternion closure maps into the actual marked even point core. -/
theorem closure_image_le_pointCore (h : D.Hypothesis) (b : Conclusions D M 6 g)
    (a : alternatingGroup (Fin 6))
    (ha : Section07.NaturalAction.image d D.V₁ = move a.val canonicalLine) :
    (D.UH.subgroupOf D.L).map (localMap d) ≤
      pointCoreEven.map (MulAut.conj a.val).toMonoidHom := by
  let J := D.L ⊓ D.Gz
  have hJ : J ≤ D.L := inf_le_left
  have hU : D.UH ≤ J.pCoreIn 2 := by
    rw [← b.five.1]
    apply pCoreIn_mono_of_normalizes (map_subtype_le _)
    exact J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pResidual 2 J))
  have hcore : (J.pCoreIn 2).subgroupOf D.L = (J.subgroupOf D.L).pCoreIn 2 := by
    apply map_injective D.L.subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 J).trans hJ),
      map_pCoreIn_of_injective 2 _ D.L.subtype D.L.subtype_injective,
      map_subgroupOf_eq_of_le hJ]
  have himage : (J.subgroupOf D.L).map (localMap d) =
      L1.map (MulAut.conj a.val).toMonoidHom := by
    have hJdef : J = D.L ⊓ normalizer (D.V₁ : Set G) :=
      congrArg (D.L ⊓ ·) h.normalizer_point_eq.symm
    rw [hJdef, localNormalizer_image d D.V₁
      (h.point_lt.le.trans h.plus_le), ha, flagStabilizer_move, flagStabilizer_line]
    rw [L1, map_inf _ _ _ (MulAut.conj a.val).injective, conjugate_alternating]
    exact inf_comm _ _
  have hh := map_mono (f := localMap d) (subgroupOf_mono D.L hU)
  rw [hcore, map_pCoreIn_of_ker_isPGroup (localMap d)
    (localMap_kernel_two d (b.four.2 rfl)), himage,
    ← map_pCoreIn_of_injective 2 L1 _ (MulAut.conj a.val).injective,
    L1_core_eq_pointCoreEven] at hh
  exact hh

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane
end
