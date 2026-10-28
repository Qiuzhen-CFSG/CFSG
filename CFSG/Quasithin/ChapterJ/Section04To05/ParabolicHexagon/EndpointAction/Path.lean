module
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortFix
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.PathTransport
/-!
# The original endpoint centralizer fixes the fourth point

The known full Ree first parabolic centralizes z and the conjugate fourth
parabolic centralizes u. Thus C_first(u) fixes both ends of the marked
four-edge path in the model. The nine-path cycle bound makes that path
unique; common pushout coverings then transfer its pointwise stabilizer to
every faithful completion, with the original endpoint maps unchanged.

Mapping the resulting containment into the source group gives
F1 ∩ C(u) ≤ F1^(fourth word), and the same word sends z to u. No Small
hypothesis or global recognition of the completion is used.
Source: Aschbacher--Smith F.4.6 and J.4.7--10, printed pp.276,443--445.
-/

public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.EndpointAction
open Subgroup Theory.GroupTheory
open Tits.ExceptionalParabolics.FullRee Tits.ExceptionalParabolics.FullRee.LongRootPaths
open ChapterF.SourceCompletion.BinaryRee
open Subgroup.CosetGeometry.RankTwo SimpleGraph SimpleGraph.BasedWalk
local notation "α" => amalgam
local notation "UComp" => RankTwoAmalgam.Universal.completion α modelCompletion
local notation "UF" => RankTwoAmalgam.Universal.cosetFamily α
private theorem gcd_model : (Nat.card first).gcd (Nat.card second)=Nat.card B := by
  rw [first_card,second_card,borel_card]
  norm_num

private theorem model_fourth_fix (a:first) (ha : (a:ReeF4.Model 0)*u=u*a) :
    (a:ReeF4.Model 0) ∈ stabilizer modelCompletion.family
      (completionFourthWord modelCompletion • base modelCompletion.family false) := by
  rw [stabilizer_translate]
  have hb : stabilizer modelCompletion.family (base modelCompletion.family false)=first := by
    simp only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base,modelCompletion_family,modelFamily,cond_false]
  rw [hb]
  refine ⟨fourthWord⁻¹*a*fourthWord,?_,?_⟩
  · apply first_eq_centralizer_z.symm ▸ (show fourthWord⁻¹*a*fourthWord ∈ centralizer {z} from ?_)
    rw [mem_centralizer_singleton_iff]
    have hh := congrArg (fun t:ReeF4.Model 0=>fourthWord⁻¹*t*fourthWord) ha
    rw [←fourthWord_conjugates] at hh
    convert hh using 1 <;> group
  · change completionFourthWord modelCompletion*(fourthWord⁻¹*a*fourthWord)*
      (completionFourthWord modelCompletion)⁻¹=a
    have hw : completionFourthWord modelCompletion=fourthWord := fourthWord_model
    rw [hw]
    group

private theorem lift_fourth {K:Type*} [Group K] (q:Completion K) :
    RankTwoAmalgam.Universal.lift α q (completionFourthWord UComp)=completionFourthWord q := by
  change RankTwoAmalgam.Universal.lift α q
    (RankTwoAmalgam.Universal.right α rightReflection *
      RankTwoAmalgam.Universal.left α leftReflection *
        RankTwoAmalgam.Universal.right α rightReflection)=_
  simp only [map_mul,RankTwoAmalgam.Universal.lift_left,RankTwoAmalgam.Universal.lift_right]
  rfl

theorem completion_centralizer_fixes_fourth {K:Type*} [Group K] (q:Completion K)
    (a:first) (ha : (a:ReeF4.Model 0)*u=u*a) :
    q.left a ∈ stabilizer q.family (completionFourthWord q • base q.family false) := by
  let p : BasedWalk (graph UF) 4 (base UF false) := completionFourPath UComp
  let cm := RankTwoAmalgam.Universal.coverData α gcd_model modelCompletion
  let cq := RankTwoAmalgam.Universal.coverData α gcd_model q
  let pm : BasedWalk (graph modelCompletion.family) 4 (cm.vertex (base UF false)) := cm.pathEquiv 4 (base UF false) p
  have hpm : pm.Nonbacktracking := by
    change (p.map cm.hom).Nonbacktracking
    exact (nonbacktracking_map_iff cm.hom (fun v=>(cm.neighbor_bijective v).1) p).mpr
      (completionFourPath_nonbacktracking UComp)
  have hpme : pm.endpoint=completionFourthWord modelCompletion • base modelCompletion.family false := by
    change (p.map cm.hom).endpoint=_
    rw [endpoint_map]
    change cm.vertex p.endpoint=_
    rw [show p.endpoint=completionFourthWord UComp • base UF false from rfl,
      cm.vertex_smul,cm.vertex_base,lift_fourth]
    rfl
  have hma : (a:ReeF4.Model 0) • cm.vertex (base UF false)=cm.vertex (base UF false) := by
    rw [cm.vertex_base]
    change (a:ReeF4.Model 0) ∈ stabilizer modelCompletion.family (base modelCompletion.family false)
    simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base,
      modelCompletion_family,modelFamily,cond_false] using a.property
  have hfix : (a:ReeF4.Model 0) ∈ pathStabilizer modelCompletion.family pm := by
    apply fixes_short_walk modelCompletion.cycle_length_gt_nine pm hpm (by decide)
      (Subgroup.CosetGeometry.translationGraphIso modelCompletion.family (a:ReeF4.Model 0)) hma
    change (a:ReeF4.Model 0) • pm.endpoint=pm.endpoint
    rw [hpme]
    exact model_fourth_fix a ha
  have hu : RankTwoAmalgam.Universal.left α a ∈ stabilizer UF (base UF false) := by
    simp only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base]
    exact ⟨a,rfl⟩
  have hup : RankTwoAmalgam.Universal.left α a ∈ pathStabilizer UF p := by
    apply (cm.fixes_path_iff ⟨_,hu⟩ p).mp
    change RankTwoAmalgam.Universal.lift α modelCompletion (RankTwoAmalgam.Universal.left α a) ∈ _
    rw [RankTwoAmalgam.Universal.lift_left]
    exact hfix
  have hend : p.endpoint ∈ p.vertices := by
    change completionFourthWord UComp • base UF false ∈
      [base UF false,base UF true,(UComp).right rightReflection • base UF false,
       ((UComp).right rightReflection*(UComp).left leftReflection) • base UF true,
       completionFourthWord UComp • base UF false]
    simp
  have hh := congrArg cq.vertex (hup p.endpoint hend)
  rw [cq.vertex_smul,RankTwoAmalgam.Universal.lift_left] at hh
  have heq : cq.vertex p.endpoint=completionFourthWord q • base q.family false := by
    change cq.vertex (completionFourthWord UComp • base UF false)=_
    rw [cq.vertex_smul,cq.vertex_base,lift_fourth]
    rfl
  rwa [heq] at hh
open MarkedInverter
variable {K:Type*} [Group K] (q:Completion K)
  {G:Type*} [Group G] {F:Subgroup G} (e:first≃*F) (f:K→*G)
  (hleft:∀a:first,f (q.left a)=(e a:G))
include hleft

theorem source_centralizer_le_fourth :
    F ⊓ centralizer {sourceU e} ≤ F.conjBy (f (completionFourthWord q)) := by
  rintro x ⟨hxF,hxu⟩
  obtain ⟨a,ha⟩ := e.surjective ⟨x,hxF⟩
  have hxa : (e a:G)=x := congrArg Subtype.val ha
  have hac : a*modelU=modelU*a := by
    apply e.injective
    apply Subtype.ext
    simpa only [map_mul,coe_mul,hxa,sourceU] using mem_centralizer_singleton_iff.mp hxu
  have hh := completion_centralizer_fixes_fourth q a (congrArg Subtype.val hac)
  rw [stabilizer_translate] at hh
  simp only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] at hh
  obtain ⟨b,hb,he⟩ := hh
  obtain ⟨a',rfl⟩ := hb
  refine ⟨(e a':G),(e a').property,?_⟩
  have he' := congrArg f he
  change f (completionFourthWord q)*(e a':G)*(f (completionFourthWord q))⁻¹=x
  simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv,hleft,hxa] using he'

theorem source_fourth_conjugates (z:G) (hz:(e modelZ:G)=z) :
    f (completionFourthWord q)*z*(f (completionFourthWord q))⁻¹=sourceU e := by
  have hh := completion_conjugates q
  change completionFourthWord q*q.left (amalgam.left (middleRoot 9))*
    (completionFourthWord q)⁻¹=q.left (amalgam.left (middleRootOne^2)) at hh
  rw [←PathTransport.modelZ_middle,←PathTransport.modelU_middle] at hh
  have he := congrArg f hh
  simpa only [map_mul,map_inv,hleft,hz,sourceU] using he

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.EndpointAction
