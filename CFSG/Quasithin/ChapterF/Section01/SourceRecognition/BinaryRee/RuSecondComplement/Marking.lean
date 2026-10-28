module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondCubicNormalizer.Basic

/-!
# Cubic coordinates retaining the selected source subgroup

Normalize the action of a generator of the supplied X on the original A.
Conjugacy of order-three core automorphisms gives the native cubic, replacing
the generator by its inverse if needed. The actual selected X and F₂ remain
unchanged, so downstream amalgam recognition keeps both source endpoints.

Source: the binary Ree branch of F.1.12 applied to J.4.5.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

theorem SourceChoice.secondCubicMarking_with_X (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic)
    (hm:Nonempty (((p.F₂ B5 X)⧸(p.A B5).subgroupOf (p.F₂ B5 X))≃*Equiv.Perm (Fin 3))) :
    ∃m:SecondCubicMarking (p:=p) B5,m.X=X := by
  obtain ⟨_,e,_⟩:=s.exists_T_F_A_marking B5 hi
  let _ : Fact (Nat.Prime 3):=⟨by decide⟩
  obtain ⟨x,hx⟩:=exists_prime_orderOf_dvd_card' (G:=X) 3
    (by rw [p.card_sylow_three X])
  have ho:=s.secondCoreAction_order_three B5 hi X hm e x hx
  obtain ⟨α,hα⟩:=ReeTwo.SylowModel.firstParabolic_cubic_conjugacy
    (secondCoreAction B5 e (x:p.parabolic)) ReeTwo.SylowModel.CubicAction.cubic ho ReeTwo.SylowModel.CubicAction.cubic_order
  have norm (y:X) (hy:orderOf y=3)
      (he:α*secondCoreAction B5 e (y:p.parabolic)*α⁻¹=ReeTwo.SylowModel.CubicAction.cubic) :
      ∃(e' : p.A B5 ≃* ReeTwo.SylowModel.firstParabolicCore) (y:X),
      orderOf y=3 ∧ ∀a : ReeTwo.SylowModel.firstParabolicCore,
        (e'.symm (ReeTwo.SylowModel.CubicAction.cubic a):G)=((y:p.parabolic):G)*(e'.symm a:G)*((y:p.parabolic):G)⁻¹ := by
    refine ⟨e.trans α,y,hy,?_⟩
    intro a
    have hh:=secondCoreAction_apply B5 e (y:p.parabolic) (e.symm (α.symm a))
    rw [e.apply_symm_apply] at hh
    have ha : α.symm (ReeTwo.SylowModel.CubicAction.cubic a)=secondCoreAction B5 e (y:p.parabolic) (α.symm a) := by
      rw [←he]
      simp only [MulAut.mul_apply,MulAut.inv_apply,MulEquiv.symm_apply_apply]
    change (e.symm (α.symm (ReeTwo.SylowModel.CubicAction.cubic a)):G)=_
    rw [ha]
    exact hh
  rcases hα with hα|hα
  · obtain ⟨e',y,hy,he⟩:=norm x hx hα
    exact ⟨⟨X,e',y,hm,hy,he⟩,rfl⟩
  · have hinv : α*secondCoreAction B5 e ((x⁻¹:X):p.parabolic)*α⁻¹=ReeTwo.SylowModel.CubicAction.cubic := by
      have hh:=congrArg Inv.inv hα
      change α*secondCoreAction B5 e ((x:p.parabolic)⁻¹)*α⁻¹=ReeTwo.SylowModel.CubicAction.cubic
      rw [map_inv]
      simpa only [mul_inv_rev,inv_inv,mul_assoc] using hh
    obtain ⟨e',y,hy,he⟩:=norm x⁻¹ (by simpa only [orderOf_inv] using hx) hinv
    exact ⟨⟨X,e',y,hm,hy,he⟩,rfl⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
