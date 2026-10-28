module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.LineCenter
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.Source

/-!
# The long-root center in the marked unitary-five carrier

The canonical line residual is the actual radical--SU₃ subgroup. Its center
has order four, and the literal cubic torus is transitive on its nonidentity
elements. Restricting the original residual inclusion transfers both statements
to the same projective carrier used by the model amalgam.

Source: Aschbacher--Smith F.4.27(4), F.4.34 and 5.3.3(b), printed pp.288,
291 and659. The Chapter6 companion uses the actual right endpoint equivalence.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
open Theory.SpecificGroups.UnitaryFive
variable (U : Model 4)

theorem leftLocalImage_center_card : Nat.card (center U.leftLocalImage) = 4 := by
  rw [←Nat.card_congr (centerCongr U.leftLocalImageEquiv).toEquiv]
  rw [U.leftLocal_eq_lineRadicalLeviSubgroup]
  obtain ⟨c,hc⟩ := U.exists_lineTraceOne
  exact LineCore.Parabolic.center_card U.form U.matrix U.conjugation U.local_field_card c hc

theorem leftLocalImage_center_orbit :
    ∀ x ∈ (center U.leftLocalImage).map U.leftLocalImage.subtype, x ≠ 1 →
      ∀ y ∈ (center U.leftLocalImage).map U.leftLocalImage.subtype, y ≠ 1 →
        ∃ g ∈ U.leftParabolic, y = g*x*g⁻¹ := by
  obtain ⟨c,hc⟩ := U.exists_lineTraceOne
  have ho : ∀ x ∈ (center U.leftLocal).map U.leftLocal.subtype, x ≠ 1 →
      ∀ y ∈ (center U.leftLocal).map U.leftLocal.subtype, y ≠ 1 →
        ∃ g : U.leftParabolic, y = g*x*g⁻¹ := by
    rw [U.leftLocal_eq_lineRadicalLeviSubgroup]
    exact LineCore.Parabolic.center_orbit U.form U.matrix U.conjugation U.local_field_card c hc
  rintro x ⟨x,hx,rfl⟩ hx1 y ⟨y,hy,rfl⟩ hy1
  let ex := (centerCongr U.leftLocalImageEquiv).symm ⟨x,hx⟩
  let ey := (centerCongr U.leftLocalImageEquiv).symm ⟨y,hy⟩
  have hex : (ex.val.val : U.Carrier) = x.val :=
    congrArg (fun z : U.leftLocalImage => z.val) (U.leftLocalImageEquiv.apply_symm_apply x)
  have hey : (ey.val.val : U.Carrier) = y.val :=
    congrArg (fun z : U.leftLocalImage => z.val) (U.leftLocalImageEquiv.apply_symm_apply y)
  have hex1 : ex.val.val ≠ 1 := fun he => hx1
    (hex.symm.trans (congrArg Subtype.val he))
  have hey1 : ey.val.val ≠ 1 := fun he => hy1
    (hey.symm.trans (congrArg Subtype.val he))
  obtain ⟨g,hg⟩ := ho ex.val.val ⟨ex.val,ex.property,rfl⟩ hex1
    ey.val.val ⟨ey.val,ey.property,rfl⟩ hey1
  refine ⟨g,g.property,?_⟩
  have hh := congrArg (fun v : U.leftParabolic => v.val) hg
  change (ey.val.val : U.Carrier) = (g : U.Carrier) * (ex.val.val : U.Carrier) *
    (g : U.Carrier)⁻¹ at hh
  rw [hex,hey] at hh
  change (y : U.Carrier) = (g : U.Carrier) * (x : U.Carrier) * (g : U.Carrier)⁻¹
  exact hh

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
