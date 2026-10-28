module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondInvolutionEscape

/-!
# Excluding the twisted second-parabolic lift

An element with the native twisted action and root-seven square has order dividing
four.  Conjugate its cyclic subgroup into the original common Sylow two-subgroup,
transport the core coordinates by the same conjugator, and use the checked
involution obstruction there.  This supplies the bad-extension exclusion in the
binary Ree case of F.1.12, applied to the actual second parabolic of J.4.5.
-/

public section
noncomputable section
open Subgroup MulAction
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

/-- The twisted lift is impossible anywhere in the original second endpoint. -/
theorem SourceChoice.no_twisted_F₂_lift (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic)
    (hm:Nonempty (((p.F₂ B5 X)⧸(p.A B5).subgroupOf (p.F₂ B5 X))≃*Equiv.Perm (Fin 3)))
    (e:p.A B5≃*ReeTwo.SylowModel.CubicAction.A)
    (v:p.F₂ B5 X) (hv:(v:G)∉p.A B5)
    (hact:∀a:p.A B5,(e.symm (ReeTwo.SylowModel.CubicAction.badActor (e a)):G)=
      (v:G)*(a:G)*(v:G)⁻¹)
    (hsq:(v:G)^2=(e.symm (ReeTwo.SylowModel.CubicAction.generator 7):G)) : False := by
  have hv4:v^4=1 := by
    apply Subtype.ext
    change (v:G)^4=1
    rw [show 4=2*2 from rfl,pow_mul,hsq,←Subgroup.coe_pow,←map_pow]
    have hz:(ReeTwo.SylowModel.CubicAction.generator 7)^2=1 := by decide +kernel
    rw [hz,map_one,Subgroup.coe_one]
  have hcyc:IsPGroup 2 (zpowers v) := IsPGroup.of_card_dvd_pow (n:=2) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hv4)
  obtain ⟨Q,hQ⟩:=hcyc.exists_le_sylow
  obtain ⟨T,hT⟩:=s.T_F_sylow_F₂ p B5 hi X hm
  obtain ⟨g,hg⟩:=exists_smul_eq (p.F₂ B5 X) Q T
  have hmap:(Q:Subgroup (p.F₂ B5 X)).map (MulAut.conj g).toMonoidHom=
      (p.T_F B5).subgroupOf (p.F₂ B5 X) := by
    have h:=congrArg Sylow.toSubgroup hg
    rw [Sylow.smul_def,Sylow.pointwise_smul_def,Subgroup.pointwise_smul_def,hT] at h
    exact h
  have hvT:(g:G)*(v:G)*(g:G)⁻¹∈p.T_F B5 := by
    have hmem:MulAut.conj g v∈(Q:Subgroup (p.F₂ B5 X)).map (MulAut.conj g).toMonoidHom :=
      ⟨v,hQ (mem_zpowers v),rfl⟩
    rw [hmap] at hmem
    exact hmem
  have hgA:(g:G)∈normalizer (p.A B5:Set G) :=
    p.A_normalized B5 (p.F₂_le_parabolic B5 X g.property)
  let κ:MulAut (p.A B5):=(p.A B5).normalizerMonoidHom ⟨g,hgA⟩
  let e':p.A B5≃*ReeTwo.SylowModel.CubicAction.A:=κ.symm.trans e
  let v':p.T_F B5:=⟨(g:G)*(v:G)*(g:G)⁻¹,hvT⟩
  have hk (a:p.A B5):(κ a:G)=(g:G)*(a:G)*(g:G)⁻¹:=rfl
  have hv':(v':G)∉p.A B5 := by
    intro h
    apply hv
    exact (mem_normalizer_iff.mp hgA (v:G)).mpr h
  apply s.no_twisted_middle_lift B5 hi e' v' hv'
  · intro a
    change (κ (e.symm (ReeTwo.SylowModel.CubicAction.badActor (e (κ.symm a)))):G)=_
    rw [hk,hact]
    have ha:(a:G)=(g:G)*(κ.symm a:G)*(g:G)⁻¹ :=
      (congrArg (fun y:p.A B5=>(y:G)) (κ.apply_symm_apply a)).symm
    change (g:G)*((v:G)*(κ.symm a:G)*(v:G)⁻¹)*(g:G)⁻¹=
      ((g:G)*(v:G)*(g:G)⁻¹)*(a:G)*((g:G)*(v:G)*(g:G)⁻¹)⁻¹
    rw [ha]
    group
  · change ((g:G)*(v:G)*(g:G)⁻¹)^2=(κ (e.symm (ReeTwo.SylowModel.CubicAction.generator 7)):G)
    rw [hk]
    calc
      ((g:G)*(v:G)*(g:G)⁻¹)^2=(g:G)*(v:G)^2*(g:G)⁻¹ := by
        simp only [pow_two]
        group
      _ = _ := by rw [hsq]

end CFSG.Quasithin.ChapterJ.RuSubgroup
