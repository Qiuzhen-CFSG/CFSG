module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuSecondInvolutionEscape.Endpoint

/-!
# The twisted action admits no source second-endpoint lift

The previous exclusion treats lifts outside A. A lift inside A would make its
inverse solve the same checked twisted-square equation, so that case is
impossible as well. This is the exact source obstruction used by the native
normalizer alternatives in F.1.12/J.4.5.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices ReeTwo.SylowModel.CubicAction
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

theorem SourceChoice.no_twisted_F₂_element (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹)
    (X:Sylow 3 p.parabolic)
    (hm:Nonempty (((p.F₂ B5 X)⧸(p.A B5).subgroupOf (p.F₂ B5 X))≃*Equiv.Perm (Fin 3)))
    (e:p.A B5≃*A) (v:p.F₂ B5 X)
    (hact:∀a:p.A B5,(e.symm (badActor (e a)):G)=(v:G)*(a:G)*(v:G)⁻¹)
    (hsq:(v:G)^2=(e.symm (generator 7):G)) : False := by
  apply s.no_twisted_F₂_lift B5 hi X hm e v _ hact hsq
  intro hv
  let a:p.A B5:=⟨(v:G)⁻¹,(p.A B5).inv_mem hv⟩
  apply ReeTwo.SylowModel.CollectedBitVectors.bad_coset_square_ne_one (e a)
  apply e.symm.injective
  apply Subtype.ext
  simp only [map_mul,map_one,e.symm_apply_apply,Subgroup.coe_mul,Subgroup.coe_one]
  rw [hact,←hsq]
  change (v:G)⁻¹*((v:G)*(v:G)⁻¹*(v:G)⁻¹)*(v:G)^2=1
  group
end CFSG.Quasithin.ChapterJ.RuSubgroup
