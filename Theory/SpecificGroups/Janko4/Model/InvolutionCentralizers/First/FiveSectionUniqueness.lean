module
public import Theory.Mathieu.M22.Properties.LocalA5Placement.Uniqueness
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.OddActor

/-!
# Uniqueness of the local A₅ residual in the first J₄ centralizer

The same full Sylow gives equal M₂₂ images by the quintet-core uniqueness
calculation. First lift equality through the central scalar kernel, then
through the two-core, which the Sylow normalizes. In both steps the perfect
subgroup is recovered as the solvable residual of its literal preimage.
The index-two cover preimage contains every perfect subgroup, so the result
also holds in the full first involution centralizer.

Source: Aschbacher--Smith A.3.14(10) and 5.1.13, printed pp.49--50,637.
-/

public noncomputable section
open Subgroup Sporadic.Mathieu
namespace Janko4.InvolutionCentralizers.First.QuotientExtension
attribute [local irreducible] modelGroup matrixA matrixB

private theorem perfect_eq_of_image_eq {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) [Group.IsSolvable f.ker] (B C : Subgroup X)
    [Group.IsPerfect B] [Group.IsPerfect C]
    (hB : f.ker ≤ normalizer (B : Set X)) (hC : f.ker ≤ normalizer (C : Set X))
    (he : B.map f = C.map f) : B = C := by
  have hh := congrArg (comap f) he
  rw [comap_map_eq,comap_map_eq] at hh
  rw [←map_solvableResidual_sup_eq_of_perfect_normalized B f.ker hB,
    ←map_solvableResidual_sup_eq_of_perfect_normalized C f.ker hC,hh]

private theorem mathieu_kernel_solvable : Group.IsSolvable mathieuProjection.ker := by
  let : Group.IsSolvable coverProjection.ker := by
    rw [coverProjection_ker]
    let : Group.IsNilpotent (Q.subgroupOf H) := pCore_isPGroup.comap_subtype.isNilpotent
    infer_instance
  let : Group.IsSolvable coverCentralProjection.ker := by
    rw [coverCentralProjection_ker]
    exact Group.isSolvable_of_comm fun x y => Subtype.ext (mem_center_iff.mp y.property x)
  rw [mathieuProjection,←MonoidHom.comap_ker]
  exact isSolvable_comap_of_solvable_ker _ _

private theorem mathieu_image_eq (S : Sylow 2 H) (B C : Subgroup H)
    [Group.IsPerfect B] [Group.IsPerfect C]
    (hB : (S : Subgroup H) ≤ normalizer (B : Set H))
    (hC : (S : Subgroup H) ≤ normalizer (C : Set H))
    (eB : B ⧸ pCore 2 B ≃* alternatingGroup (Fin 5))
    (eC : C ⧸ pCore 2 C ≃* alternatingGroup (Fin 5)) :
    B.map mathieuProjection = C.map mathieuProjection := by
  let f := mathieuProjection
  let : Group.IsSolvable f.ker := mathieu_kernel_solvable
  have mark (R : Subgroup H) [Group.IsPerfect R]
      (e : R ⧸ pCore 2 R ≃* alternatingGroup (Fin 5)) :
      (R.map f) ⧸ pCore 2 (R.map f) ≃* alternatingGroup (Fin 5) := by
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsSimpleGroup (R ⧸ pCore 2 R) := e.isSimpleGroup
    let k := f.subgroupMap R
    let : Group.IsSolvable k.ker := by
      rw [show k.ker = f.ker.comap R.subtype from Subgroup.ker_subgroupMap R f]
      exact Group.isSolvable_of_isSolvable_injective
        (f := R.subtype.subgroupComap f.ker)
        (fun x y hh => Subtype.ext (Subtype.ext (congrArg (fun t : f.ker => (t : H)) hh)))
    exact (Theory.GroupTheory.PerfectCoreTwoExtension.solvableKernelQuotientEquiv k
      (f.subgroupMap_surjective R)).symm.trans e
  let : Group.IsPerfect (B.map f) := Group.IsPerfect.map _
  let : Group.IsPerfect (C.map f) := Group.IsPerfect.map _
  exact M22LocalA5Placement.eq_of_normalized
    (S.mapSurjective (f := f) mathieuProjection_surjective) (B.map f) (C.map f)
    ((map_mono hB).trans (B.le_normalizer_map f))
    ((map_mono hC).trans (C.le_normalizer_map f)) (mark B eB) (mark C eC)

/-- In the actual cover preimage, a full Sylow determines the same perfect A₅ section. -/
theorem cover_five_section_unique (S : Sylow 2 H) (B C : Subgroup H)
    [Group.IsPerfect B] [Group.IsPerfect C]
    (hB : (S : Subgroup H) ≤ normalizer (B : Set H))
    (hC : (S : Subgroup H) ≤ normalizer (C : Set H))
    (eB : B ⧸ pCore 2 B ≃* alternatingGroup (Fin 5))
    (eC : C ⧸ pCore 2 C ≃* alternatingGroup (Fin 5)) : B = C := by
  have hm := mathieu_image_eq S B C hB hC eB eC
  let : Group.IsSolvable coverCentralProjection.ker := by
    rw [coverCentralProjection_ker]
    exact Group.isSolvable_of_comm fun x y => Subtype.ext (mem_center_iff.mp y.property x)
  let : Group.IsPerfect (B.map coverProjection) := Group.IsPerfect.map _
  let : Group.IsPerfect (C.map coverProjection) := Group.IsPerfect.map _
  have he : B.map coverProjection = C.map coverProjection := by
    apply perfect_eq_of_image_eq coverCentralProjection
    · rw [coverCentralProjection_ker]; exact center_le_normalizer _
    · rw [coverCentralProjection_ker]; exact center_le_normalizer _
    · simpa only [mathieuProjection,map_map] using hm
  have hk : IsPGroup 2 coverProjection.ker := by
    rw [coverProjection_ker]
    exact pCore_isPGroup.comap_subtype
  let : Group.IsNilpotent coverProjection.ker := hk.isNilpotent
  exact perfect_eq_of_image_eq coverProjection B C
    ((hk.le_sylow_of_normal S).trans hB) ((hk.le_sylow_of_normal S).trans hC) he

/-- In the full first centralizer, a full Sylow determines the perfect A₅ section. -/
theorem five_section_unique (S : Sylow 2 centralizer) (B C : Subgroup centralizer)
    [Group.IsPerfect B] [Group.IsPerfect C]
    (hB : (S : Subgroup centralizer) ≤ normalizer (B : Set centralizer))
    (hC : (S : Subgroup centralizer) ≤ normalizer (C : Set centralizer))
    (eB : B ⧸ pCore 2 B ≃* alternatingGroup (Fin 5))
    (eC : C ⧸ pCore 2 C ≃* alternatingGroup (Fin 5)) : B = C := by
  let : Group.IsSolvable (centralizer ⧸ H) := Group.isSolvable_of_surjective
    (f := centralizerQuotientEquivC2.symm.toMonoidHom) centralizerQuotientEquivC2.symm.surjective
  have hBH : B ≤ H := le_of_isPerfect_of_solvable_quotient B H
  have hCH : C ≤ H := le_of_isPerfect_of_solvable_quotient C H
  let dB := subgroupOfEquivOfLe hBH
  let dC := subgroupOfEquivOfLe hCH
  let : Group.IsPerfect (B.subgroupOf H) := Group.IsPerfect.ofSurjective
    (f := dB.symm.toMonoidHom) dB.symm.surjective
  let : Group.IsPerfect (C.subgroupOf H) := Group.IsPerfect.ofSurjective
    (f := dC.symm.toMonoidHom) dC.symm.surjective
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal H
  have he := cover_five_section_unique P (B.subgroupOf H) (C.subgroupOf H)
    (by rw [hP,←subgroupOf_normalizer_eq hBH]; exact comap_mono hB)
    (by rw [hP,←subgroupOf_normalizer_eq hCH]; exact comap_mono hC)
    ((QuotientGroup.congr _ _ dB (pCore_map_iso 2 dB)).trans eB)
    ((QuotientGroup.congr _ _ dC (pCore_map_iso 2 dC)).trans eC)
  have hh := congrArg (map H.subtype) he
  simpa only [map_subgroupOf_eq_of_le hBH,map_subgroupOf_eq_of_le hCH] using hh
end Janko4.InvolutionCentralizers.First.QuotientExtension
