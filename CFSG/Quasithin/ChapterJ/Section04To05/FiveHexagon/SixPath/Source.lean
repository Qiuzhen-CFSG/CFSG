module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.SixPath
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedShortNatural

/-!
# The six-geodesic commutator in the same original second parabolic

The source centered six-geodesic has the literal root-five and root-one-square
labels. Compatibility of the original second endpoint map identifies them
with modelLeft and modelRight under that same map. The already proved local
calculation then places their commutator in the original natural V and gives
the actual A times centralizer supplement in F2. No V-placement, short-root
recognition, or whole-completion equivalence is added as a premise.
Source: the final proof of J.4.7, printed p.444.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.PathTransport
open Subgroup Theory.GroupTheory
open Tits.ExceptionalParabolics.FullRee Tits.ExceptionalParabolics.FullRee.LongRootPaths
open ChapterF.SourceCompletion.BinaryRee
open MarkedInverter MarkedSecondCore
open Subgroup.CosetGeometry.RankTwo
variable {D : Type*} [Group D] (q : Completion D)
  {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)
  (B5 : Sylow 5 d.toTypeRuSetup.H) (X : Sylow 3 p.parabolic)
  (h : Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3)))
  (e : second ≃* p.F₂ B5 X) (f : D →* G)
  (hright : ∀ a : second, f (q.right a)=(e a : G))

private theorem modelLeft_middle : modelLeft=amalgam.right (middleRoot 5) :=
  Subtype.ext leftSix_eq_rootfive

private theorem modelRight_middle : modelRight=amalgam.right (middleRootOne^2) :=
  Subtype.ext middleRootOne_square_coe.symm

include hright in
/-- The first six-geodesic label uses the exact original second endpoint map. -/
theorem source_six_left :
    f (completionLeftWord q*q.left modelZ*(completionLeftWord q)⁻¹)=(e modelLeft : G) := by
  rw [modelZ_middle]
  change f (completionLeftWord q*q.middle (middleRoot 9)*(completionLeftWord q)⁻¹)=_
  rw [completion_leftSix_conjugates,modelLeft_middle]
  have hc := DFunLike.congr_fun q.compatible (middleRoot 5)
  rw [hc,MonoidHom.comp_apply,hright]

include hright in
/-- The other endpoint is the same original image of the marked root-one square. -/
theorem source_six_right : f (q.left modelU)=(e modelRight : G) := by
  rw [modelU_middle]
  change f (q.middle (middleRootOne^2))=_
  have hc := DFunLike.congr_fun q.compatible (middleRootOne^2)
  rw [hc,MonoidHom.comp_apply,hright,modelRight_middle]

include h hright in
/-- The actual geodesic labels, their commutator and the source supplement
all retain the same original endpoint embedding. -/
theorem source_six_commutator_data :
    q.graph.dist (completionLeftWord q • basePoint q) (completionFourthWord q • basePoint q)=6 ∧
    let z0 := f (completionLeftWord q*q.left modelZ*(completionLeftWord q)⁻¹)
    let z3 := f (q.left modelU)
    let t := z0*z3*z0⁻¹*z3⁻¹
    z0=(e modelLeft : G) ∧ z3=(e modelRight : G) ∧ t=(e modelShort : G) ∧
      z0∈p.A B5 ∧ z3∈p.A B5 ∧ orderOf (z0*z3)=4 ∧ t∈d.V ∧
      p.A B5 ⊔ (p.F₂ B5 X ⊓ centralizer ({t} : Set G))=p.F₂ B5 X := by
  refine ⟨centered_six_distance q,?_⟩
  dsimp only
  rw [source_six_left q p B5 X e f hright,source_six_right q p B5 X e f hright,
    source_commutator p B5 X e]
  obtain ⟨hl,hr,_⟩ := source_endpoints_mem_A p B5 X h e
  obtain ⟨ht,hsup⟩ := source_short_natural_and_supplement p B5 X h e
  refine ⟨rfl,rfl,rfl,hl,hr,?_,ht,hsup⟩
  have hm : orderOf (modelLeft*modelRight)=4 :=
    (orderOf_injective second.subtype second.subtype_injective _).symm.trans leftSix_mul_u_order
  have hf : Function.Injective ((p.F₂ B5 X).subtype.comp e.toMonoidHom) :=
    (p.F₂ B5 X).subtype_injective.comp e.injective
  have hh := orderOf_injective ((p.F₂ B5 X).subtype.comp e.toMonoidHom) hf (modelLeft*modelRight)
  simpa only [MonoidHom.comp_apply,map_mul,coe_mul,Subgroup.subtype_apply,MulEquiv.coe_toMonoidHom] using hh.trans hm

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.PathTransport
