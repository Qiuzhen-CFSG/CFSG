module
public import Theory.SpecificGroups.SymplecticFour.RetainedPointIntersection
public import Theory.SpecificGroups.SymplecticFour.MoverNormalizer

/-!
# The exceptional root pair at the retained point marking

A proper join with the full point projection meets the point radical centrally.
The actual large endpoint fills that center. The same incident plane marking
then yields the root pair and index two, without changing the selected mover
or conjugator. This is the full-kernel part of MS93 (5.5)(c), used on p.925.
-/

public noncomputable section
open Subgroup Matrix
namespace Theory.SpecificGroups.SymplecticFour.RetainedPointRootPair
open CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A failed generation join yields an index-two root pair for the original
mover in the same marking. No existential selector is introduced. -/
theorem original_mover_root_pair {n : ℕ} (hcard : Nat.card F=2^n) (hn : 1<n)
    (A : Subgroup (Sp F)) (E : Subgroup (unipotent (F := F)))
    (hfixed : fixed E=point F)
    (hout : ¬ E.map unipotent.subtype ≤ (CentralRootGeometry.wing true).map unipotent.subtype)
    (s w : Sp F) (hs : s∈planeLocal) (hsp : s∉pointParabolic) (hws : w*s∈pointLocal)
    (hproper : A ⊔ (E.map unipotent.subtype).map (MulAut.conj w).toMonoidHom ≠ ⊤)
    (hproj : ((A ⊔ (E.map unipotent.subtype).map (MulAut.conj w).toMonoidHom).subgroupOf
      pointLocal).map pointQuotient=⊤)
    (hcore : (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2 ≤ pointLocal)
    (hAL : A ≤ pointLocal)
    (hAproj : (A.subgroupOf pointLocal).map pointQuotient=SpecialLinearGroup.upperUnipotent F)
    (hAlarge : Nat.card F^2 ≤ Nat.card A) :
    ∃ r b : F, b≠0 ∧
      (rootImage (some r) ⊔ rootImage (some (r+b))).relIndex (E.map unipotent.subtype)=2 := by
  let N := A ⊔ (E.map unipotent.subtype).map (MulAut.conj w).toMonoidHom
  let D := N.subgroupOf pointLocal
  have hw : w∉pointParabolic := by
    intro hw
    apply hsp
    simpa only [inv_mul_cancel_left] using
      pointParabolic.mul_mem (pointParabolic.inv_mem hw) (pointLocal_le hws)
  have hD : D≠⊤ := by
    intro htop
    apply hproper
    apply PointIndividualGeneration.generate_of_pointLocal_le hcard hn A E hfixed w hw
    intro x hx
    exact (show (⟨x,hx⟩ : pointLocal) ∈ D from htop.symm ▸ mem_top _)
  have hsupp : D ⊔ pointRadical=⊤ := by
    rw [←pointQuotient_ker,←comap_map_eq]
    rw [hproj,comap_top]
  have hc := (PointSupplement.supplement_dichotomy hcard hn D hsupp).resolve_left hD
  have hsize : Nat.card F^2 ≤ Nat.card (A.subgroupOf pointLocal) := by
    rwa [←card_map_of_injective pointLocal.subtype_injective,
      map_subgroupOf_eq_of_le hAL]
  have hcentral := (PointSupplement.central_kernel_large_endpoint hcard hn D
    (A.subgroupOf pointLocal) hc (comap_mono le_sup_left) hAproj hsize).2.2.1
  obtain ⟨r,b,hb,hpair,_,hindex,_⟩ := MoverNormalizer.marked_plane_intersection_root_pair
    hcard hn N (E.map unipotent.subtype) (map_subtype_le _) hout s w hs hsp hws
    le_sup_right hcore hcentral
  refine ⟨r,b,hb,?_⟩
  have hh := relIndex_map_map_of_injective
    (N ⊓ (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2)
    ((E.map unipotent.subtype).map (MulAut.conj w).toMonoidHom)
    (f := (MulAut.conj w⁻¹).toMonoidHom) (MulAut.conj w⁻¹).injective
  rw [hpair,Subgroup.map_map] at hh
  have he : (MulAut.conj w⁻¹).toMonoidHom.comp (MulAut.conj w).toMonoidHom=MonoidHom.id _ := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [he,Subgroup.map_id] at hh
  exact hh.trans hindex

end Theory.SpecificGroups.SymplecticFour.RetainedPointRootPair
