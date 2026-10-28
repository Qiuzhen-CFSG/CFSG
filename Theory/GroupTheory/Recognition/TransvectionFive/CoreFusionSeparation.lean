module
public import Theory.GroupTheory.Recognition.TransvectionFive.CoreFusionModel
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCoordinates
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneCoordinates
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSylow

/-!
# Ambient separation of the mixed core involution

Restrict the original marked centralizer isomorphism to the common
centralizer of the point and the mixed involution. The model's second
derived line transports to the original point line, so every normalizer
of that common centralizer fixes the point. Its proper containment in
the marked Sylow then rules out conjugacy by the two-group normalizer
condition. Two explicit point-centralizer shears connect the matrix
representative to code 33 in the rectangle census.

This proves the mixed-orbit exclusion in Aschbacher, *Sporadic Groups*
(1994), 39.4, p.214. It uses only a finite group and the full marked
centralizer; simplicity and point-core fusion are unnecessary for this
exclusion. `FourRecognitionCoreSeparation` applies it to 12.2.27(1).
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.CoreFusion
open UniquenessLinear PlaneTensor CoreFusionModel
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

private theorem element34_model :
    (F.equiv ⟨element F 34,F.pullback_le _ (element_mem F 34)⟩ : SL) = mixed := by
  rw [element_model]
  change modelElement (decode 34) = mixed
  apply Subtype.ext
  rw [modelElement_matrix]
  simp [mixed,root,Matrix.SpecialLinearGroup.transvection_coe,decode,val,
    Matrix.add_mul,Matrix.mul_add,Matrix.single_mul_single_of_ne,add_assoc]

private theorem pullback_common : F.pullback common =
    Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({element F 34} : Set G) := by
  let H := Subgroup.centralizer ({z} : Set G)
  let t : H := ⟨element F 34,F.pullback_le _ (element_mem F 34)⟩
  ext x
  constructor
  · intro hx
    have hxH := F.pullback_le common hx
    have hm := (F.mem_pullback_iff common ⟨x,hxH⟩).mp hx
    refine ⟨hxH,mem_centralizer_singleton_iff.mpr ?_⟩
    have he : (⟨x,hxH⟩ : H)*t = t*⟨x,hxH⟩ := by
      apply F.equiv.injective
      apply Subtype.ext
      simp only [map_mul,Subgroup.coe_mul]
      change (F.equiv ⟨x,hxH⟩ : SL) * (F.equiv t : SL) = _
      rw [show (F.equiv t : SL) = mixed from element34_model F]
      exact mem_centralizer_singleton_iff.mp hm.2
    exact congrArg Subtype.val he
  · rintro ⟨hxH,hxt⟩
    apply (F.mem_pullback_iff common ⟨x,hxH⟩).mpr
    refine ⟨(F.equiv ⟨x,hxH⟩).property,mem_centralizer_singleton_iff.mpr ?_⟩
    have he : (⟨x,hxH⟩ : H)*t = t*⟨x,hxH⟩ :=
      Subtype.ext (mem_centralizer_singleton_iff.mp hxt)
    have hh := congrArg (fun a : H => (F.equiv a : SL)) he
    simpa only [map_mul,Subgroup.coe_mul,show (F.equiv t : SL) = mixed from element34_model F] using hh

private theorem point_mem_common : transvection ∈ common := by
  constructor
  · exact mem_centralizer_singleton_iff.mpr rfl
  · apply mem_centralizer_singleton_iff.mpr
    decide +kernel

private theorem common_derived_internal : derivedSeries common 2 =
    zpowers (⟨transvection,point_mem_common⟩ : common) := by
  apply map_injective common.subtype_injective
  rw [common_second_derived,MonoidHom.map_zpowers]
  rfl

private theorem point_mem_pullback_common : z ∈ F.pullback common := by
  apply (F.mem_pullback_iff common ⟨z,mem_centralizer_singleton_iff.mpr rfl⟩).mpr
  rw [F.on_point]
  exact point_mem_common

private theorem pullback_second_derived :
    (derivedSeries (F.pullback common) 2).map (F.pullback common).subtype = zpowers z := by
  let A := F.pullback common
  let e := F.pullbackEquiv common (show common ≤ centralizer from inf_le_left)
  let p : A := ⟨z,point_mem_pullback_common F⟩
  have hep : e p = ⟨transvection,point_mem_common⟩ := Subtype.ext F.on_point
  have hi : derivedSeries A 2 = zpowers p := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_derivedSeries_eq e.surjective,common_derived_internal,
      MonoidHom.map_zpowers]
    exact (congrArg zpowers hep).symm
  rw [hi,MonoidHom.map_zpowers]
  rfl

variable [Finite G]

/-- Source 39.4 for the mixed core representative, under the original marking. -/
theorem not_conjugate_mixed : ¬ IsConj z (element F 34) := by
  let A := F.pullback common
  let U := F.pullback upper
  have hAU : A ≤ U := by
    intro x hx
    have hc := F.pullback_le common hx
    apply (F.mem_pullback_iff upper ⟨x,hc⟩).mpr
    exact common_le_upper ((F.mem_pullback_iff common ⟨x,hc⟩).mp hx)
  have hUs : U = (sourceSylow F : Subgroup G) := (sourceSylow_eq_pullback_upper F).symm
  have hpA : IsPGroup 2 A := (sourceSylow F).isPGroup'.of_injective
    (inclusion (hAU.trans hUs.le)) (inclusion_injective _)
  have hcA : Nat.card A = Nat.card common := Nat.card_congr
    (F.pullbackEquiv common (show common ≤ centralizer from inf_le_left)).toEquiv
  have hcU : Nat.card U = Nat.card upper := Nat.card_congr
    (F.pullbackEquiv upper upper_le_centralizer).toEquiv
  have hlt : Nat.card A < Nat.card U := by
    rw [hcA,hcU]
    refine lt_of_le_of_ne (card_le_of_le common_le_upper) ?_
    intro he
    exact common_lt_upper.ne (eq_of_le_of_card_ge common_le_upper he.ge)
  let S := (sourceSylow F).subtype (sourceSylow_le_point_centralizer F)
  have hcS : Nat.card S = Nat.card U := by
    rw [hUs]
    exact Nat.card_congr (subgroupOfEquivOfLe (sourceSylow_le_point_centralizer F)).toEquiv
  have hN : normalizer (A : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
    normalizer_le_centralizer_of_characteristic_involution A (derivedSeries A 2)
      z F.point_orderOf (pullback_second_derived F)
  apply not_isConj_of_small_common_centralizer_normalizer (p := 2) z (element F 34)
    (by rw [← pullback_common]; exact hpA) S
  · rw [hcS,← pullback_common]
    exact hlt
  · change normalizer ((Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer ({element F 34} : Set G) : Subgroup G) : Set G) ≤ _
    rw [← pullback_common]
    exact hN

/-- The census representative 33 is in the same point-centralizer orbit as 34. -/
theorem not_conjugate_core33 : ¬ IsConj z (element F 33) := by
  obtain ⟨n,_,hn⟩ := exists_shear_conjugator F 1 33
  obtain ⟨m,_,hm⟩ := exists_shear_conjugator F 2 35
  have h1 : IsConj (element F 33) (element F 35) := isConj_iff.mpr ⟨n,hn⟩
  have h2 : IsConj (element F 35) (element F 34) := isConj_iff.mpr ⟨m,hm⟩
  exact fun h => not_conjugate_mixed F (h.trans (h1.trans h2))

end Theory.GroupTheory.TransvectionFive.CoreFusion
