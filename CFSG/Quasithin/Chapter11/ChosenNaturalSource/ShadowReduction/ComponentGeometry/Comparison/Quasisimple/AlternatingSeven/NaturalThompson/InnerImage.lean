module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson.MarkedImage
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson.InnerSylow
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.FieldAction

/-!
# The original Thompson subgroup acts inner on the marked seed

The natural parabolic projection lifts every element of T intersect L to
L1 with the same original component quotient. Its discrepancy lies in
O2(L), hence in T and in the actual quotient centralizer. The seed-image
centralizer theorem removes this discrepancy in the local action. Together
with original Thompson containment, this proves the existing
ThompsonInnerImage interface for the caller's original invariant flag.

The final application uses the independent maximum-elementary field witness.
Its construction belongs to qt-d-1222-a7-field-witness, and final A7 assembly
to qt-d-1222-quasisimple-a7. Only the permitted earlier actual L1/O2(L1)
marking remains explicit, produced by qt-d-1222-natural-flag-cartan.
Source: Aschbacher--Smith, B.4.2(2)--(4), printed p.86, and11.4.2, p.777.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

omit [Finite G] in
theorem pCoreIn_le_coreQuotientCentralizer (A : Subgroup G) :
    A.pCoreIn 2 ≤ Closure.coreQuotientCentralizer A := by
  rintro _ ⟨r,hr,rfl⟩
  refine ⟨inclusion A.le_normalizer r,MonoidHom.mem_ker.mpr ?_,rfl⟩
  apply MulEquiv.ext
  intro x
  obtain ⟨s,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) x
  rw [Closure.coreQuotientAction_apply_mk]
  change QuotientGroup.mk' (pCore 2 A) (r * s * r⁻¹) = QuotientGroup.mk' (pCore 2 A) s
  have hrq : QuotientGroup.mk' (pCore 2 A) r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
  rw [map_mul,map_mul,map_inv,hrq,one_mul,inv_one,mul_one]

theorem component_core_le_sylow (D : Chapter12.Section02.ChosenModule T L V) :
    L.pCoreIn 2 ≤ T := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L D.sylow_normalizes_component
  have hcore : pCore 2 L ≤ (T : Subgroup G).subgroupOf L :=
    hP ▸ pCore_isPGroup.le_sylow_of_normal P
  rintro _ ⟨r,hr,rfl⟩
  exact hcore hr

theorem ofFlag_innerSylowImage_le
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hmodel : AlternatingSevenModel (ofFlag S f X z H))
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      PSL(2,S.field.Carrier)) :
    innerSylowImage (ofFlag S f X z H) ≤ seedImage (ofFlag S f X z H) ⊔
      centralizer (seedImage (ofFlag S f X z H) : Set (ActionQuotient (ofFlag S f X z H))) := by
  let E := ofFlag S f X z H
  rintro _ ⟨l,hl,rfl⟩
  let lL : L := ⟨(l : G),hl.2⟩
  obtain ⟨k,hk⟩ := innerSylow_lift S f lL hl.1
  let kL : L := ⟨k,(LocalGeometry.localResidual_le _ k.property).1⟩
  let r : L := kL⁻¹ * lL
  have hr : r ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff r).mp
    change QuotientGroup.mk' (pCore 2 L) (kL⁻¹ * lL) = 1
    rw [map_mul,map_inv]
    change (QuotientGroup.mk' (pCore 2 L) kL)⁻¹ * QuotientGroup.mk' (pCore 2 L) lL = 1
    rw [show QuotientGroup.mk' (pCore 2 L) kL = QuotientGroup.mk' (pCore 2 L) lL from hk,
      inv_mul_cancel]
  have hrG : (r : G) ∈ L.pCoreIn 2 := mem_map_of_mem L.subtype hr
  have hrT := component_core_le_sylow D hrG
  let r' : localGroup E := ⟨r,(le_sup_right : (T : Subgroup G) ≤ localGroup E) hrT⟩
  let k' : localGroup E := ⟨k,((le_conjugateSpanBy _ _).trans le_sup_left) k.property⟩
  have he : l = k' * r' := by
    apply Subtype.ext
    change (lL : G) = (kL : G) * ((kL : G)⁻¹ * (lL : G))
    simp
  rw [he,map_mul]
  apply (seedImage E ⊔ centralizer (seedImage E : Set (ActionQuotient E))).mul_mem
  · exact mem_sup_left ⟨k',k.property,rfl⟩
  · exact mem_sup_right (projection_centralizes_seedImage_of_coreQuotientCentralizer
      E hstar hmodel e r' (f.sylow_normalizes_Li 0 hrT)
      (pCoreIn_le_coreQuotientCentralizer L hrG))

/-- The original natural-module result on the literal marked L1 image. -/
theorem ofFlag_thompsonInnerImage
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hmodel : AlternatingSevenModel (ofFlag S f X z H))
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      PSL(2,S.field.Carrier)) : ThompsonInnerImage (ofFlag S f X z H) := by
  intro a ha _
  exact (sup_le (ofFlag_innerSylowImage_le S f X z H hstar hmodel e) le_sup_right)
    (ofFlag_projection_mem_innerSylow_join_centralizer S f X z H hstar hmodel e a ha)

/-- Literal connection to the independent A7 field-witness consumer. -/
theorem ofFlag_false_of_maximalFieldWitness
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hmodel : AlternatingSevenModel (ofFlag S f X z H))
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      PSL(2,S.field.Carrier))
    (hfield : HasMaximalFieldWitness (ofFlag S f X z H)) : False :=
  false_of_inner_image_and_field_witness _
    (ofFlag_thompsonInnerImage S f X z H hstar hmodel e) hfield

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson
