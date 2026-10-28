module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedSecondCore
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.CubicTransport

/-!
# The cubic transporter in the original second endpoint

The same endpoint equivalence carrying the marked short commutator carries
the explicit cubic centralizer element. This retains all three literal
source marks and proves the needed order-three conjugacy without a source
orbit hypothesis. Source: the quotient-separation step of J.4.7, p.444.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedSecondCore
open Subgroup Tits.ExceptionalParabolics.FullRee
open Tits.ExceptionalParabolics.FullRee.LongRootPaths

def modelCubic : second := ⟨cubicTransporter,cubicTransporter_mem_second⟩

variable {G : Type*} [Group G] [Finite G] {d:LocalSetup G} (p:Plane d)
  (B5:Sylow 5 d.H) (X:Sylow 3 p.parabolic) (e:second≃*p.F₂ B5 X)

theorem source_cubic_transport :
    (e modelCubic:G)∈p.F₂ B5 X ∧ orderOf (e modelCubic:G)=3 ∧
    Commute (e modelCubic:G) (e modelShort:G) ∧
    (e modelCubic:G)*(e modelLeft:G)*(e modelCubic:G)⁻¹=(e modelRight:G) := by
  let f:second→*G := (p.F₂ B5 X).subtype.comp e.toMonoidHom
  have hf:Function.Injective f := Subtype.val_injective.comp e.injective
  refine ⟨(e modelCubic).property,?_,?_,?_⟩
  · have ho : orderOf modelCubic=3 :=
      (orderOf_injective second.subtype second.subtype_injective modelCubic).symm.trans cubicTransporter_order
    exact (orderOf_injective f hf modelCubic).trans ho
  · have hc:Commute modelCubic modelShort := by
      show modelCubic*modelShort=modelShort*modelCubic
      exact Subtype.ext cubicTransporter_centralizes.eq
    exact hc.map f
  · have he:modelCubic*modelLeft*modelCubic⁻¹=modelRight := Subtype.ext cubicTransporter_conj_left
    simpa only [map_mul,map_inv,f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,Subgroup.subtype_apply] using congrArg f he

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedSecondCore
