module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Counting.NaturalFree
public import Theory.GroupTheory.CommutingProductCoordinates

/-!
# The source central product coordinates

The original quaternion centralizer HB and U generate HC, with intersection Z.
Projecting U onto its given natural module U/Z therefore extends to HC with
kernel HB. This is the second binary section in J.2.7(8), printed p.437.
-/

open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d:LocalSetup G} (c:Choices d)

public theorem HB_le_HC_source : Fusion.HB d.toTypeRuSetup c.sylowThree≤d.toTypeRuSetup.HC := by
  have cp:=Fusion.centralProductData_of_quaternion d c.sylowThree (SourceCompletion.quaternion c.sylowThree)
  rw [cp.product_eq]
  exact le_sup_left

public theorem HC_coordinates_source : ∃p:d.toTypeRuSetup.HC→*Multiplicative FourSpace,
    Function.Surjective p ∧ p.ker=(Fusion.HB d.toTypeRuSetup c.sylowThree).subgroupOf d.toTypeRuSetup.HC ∧
      ∀a:Fusion.HB d.toTypeRuSetup c.sylowThree,∀b:d.toTypeRuSetup.U,
        p ⟨(a:G)*(b:G),d.toTypeRuSetup.HC.mul_mem (c.HB_le_HC_source a.property)
          (d.U_le_HC b.property)⟩=d.ru2.natural.coordinates b := by
  let C:=d.toTypeRuSetup.HC
  let A:Subgroup C:=(Fusion.HB d.toTypeRuSetup c.sylowThree).subgroupOf C
  let B:Subgroup C:=d.toTypeRuSetup.U.subgroupOf C
  let eB:B≃*d.toTypeRuSetup.U:=subgroupOfEquivOfLe d.U_le_HC
  let f:=d.ru2.natural.coordinates.comp eB.toMonoidHom
  have hcomm:∀a:A,∀b:B,Commute (a:C) (b:C) := by
    intro a b
    apply Subtype.ext
    exact ((c.HB_le_HC_source a.property).2 b b.property).symm
  have htop:A⊔B=⊤ := by
    rw [←subgroupOf_sup c.HB_le_HC_source d.U_le_HC]
    have cp:=Fusion.centralProductData_of_quaternion d c.sylowThree (SourceCompletion.quaternion c.sylowThree)
    rw [←cp.product_eq,subgroupOf_self]
  have hker (b:B) : f b=1↔(b:C)∈A := by
    change d.ru2.natural.coordinates (eB b)=1↔(((b:C):G)∈Fusion.HB d.toTypeRuSetup c.sylowThree)
    rw [d.ru2.natural.coordinates_eq_one_iff]
    have cp:=Fusion.centralProductData_of_quaternion d c.sylowThree (SourceCompletion.quaternion c.sylowThree)
    change (((b:C):G)∈d.toTypeRuSetup.Z) ↔ _
    rw [←cp.intersection_eq]
    exact and_iff_left b.property
  obtain ⟨p,hp,hpk,he⟩:=Subgroup.exists_hom_from_commuting_product A B hcomm htop f
    (d.ru2.natural.onto.comp eB.surjective) hker
  refine ⟨p,hp,hpk,?_⟩
  intro a b
  exact he ⟨⟨a,c.HB_le_HC_source a.property⟩,a.property⟩ ⟨⟨b,d.U_le_HC b.property⟩,b.property⟩

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
