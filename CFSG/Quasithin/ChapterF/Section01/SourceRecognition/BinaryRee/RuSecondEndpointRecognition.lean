module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondNativeCubic
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondEndpointRecognition
public import Theory.GroupTheory.CubicInvolutionExtension.Generation

/-!
# Whole second-parabolic recognition from the native complement

The original quotient F₂/A is S₃.  Thus an actual cubic and involutory inverter
with the specified native actions generate F₂ together with A.  Applying the
native endpoint presentation constructs a whole endpoint equivalence preserving
every original core element and both actors.  The normalizer construction
supplies these actor hypotheses in the final source theorem.

Source: Aschbacher–Smith F.1.12 applied to the original J.4.5 second parabolic.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Subgroup Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

theorem SourceChoice.F₂_equiv_of_native_complement (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic)
    (hm:Nonempty (((p.F₂ B5 X)⧸(p.A B5).subgroupOf (p.F₂ B5 X))≃*Equiv.Perm (Fin 3)))
    (e:p.A B5≃*ReeTwo.SylowModel.CubicAction.A) (c b:p.F₂ B5 X)
    (hc:orderOf c=3) (hb:b^2=1) (hbc:b*c*b⁻¹=c⁻¹)
    (hjc:∀a:ReeTwo.SylowModel.CubicAction.A,
      (e.symm (ReeTwo.SylowModel.CubicAction.cubic a):G)=(c:G)*(e.symm a:G)*(c:G)⁻¹)
    (hjb:∀a:ReeTwo.SylowModel.CubicAction.A,
      (e.symm (ReeTwo.SylowModel.CubicAction.inverter a):G)=(b:G)*(e.symm a:G)*(b:G)⁻¹) :
    ∃E:Tits.ExceptionalParabolics.FullRee.second≃*p.F₂ B5 X,
      (∀a:ReeTwo.SylowModel.CubicAction.A,
        (E (ReeTwo.SylowModel.CubicAction.coreInclusion a):G)=(e.symm a:G))∧
      E ReeTwo.SylowModel.CubicAction.element=c∧
      E Tits.AmalgamRigidity.FullRee.SecondExtension.reflection=b := by
  let j:ReeTwo.SylowModel.CubicAction.A→*p.F₂ B5 X:=
    (Subgroup.inclusion (p.A_le_F₂ B5 X)).comp e.symm.toMonoidHom
  let N:Subgroup (p.F₂ B5 X):=(p.A B5).subgroupOf (p.F₂ B5 X)
  have hj:j.range=N := by
    ext y
    constructor
    · rintro ⟨a,rfl⟩
      exact (e.symm a).property
    · intro hy
      let a:p.A B5:=⟨(y:G),hy⟩
      refine ⟨e a,?_⟩
      apply Subtype.ext
      change (e.symm (e a):G)=(y:G)
      rw [e.symm_apply_apply]
  have h6:Nat.card ((p.F₂ B5 X)⧸N)=6 := by
    obtain ⟨eqv⟩:=hm
    rw [Nat.card_congr eqv.toEquiv]
    simp only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  have hgen:=CubicInvolutionExtension.generated_eq_top_of_six_quotient N j hj c b hc hb hbc
    (p.A_isPGroup B5).comap_subtype h6
  obtain ⟨E,hE,hEc,hEb⟩:=ReeTwo.SylowModel.CubicAction.exists_endpoint_equiv_of_native_actions
    j c b (by simpa only [hc] using pow_orderOf_eq_one c) hb hbc
    (fun a=>Subtype.ext (hjc a)) (fun a=>Subtype.ext (hjb a)) hgen
    (s.card_F₂ p B5 hi X hm)
  refine ⟨E,?_,hEc,hEb⟩
  intro a
  exact congrArg (fun z:p.F₂ B5 X=>(z:G)) (hE a)

end CFSG.Quasithin.ChapterJ.RuSubgroup
