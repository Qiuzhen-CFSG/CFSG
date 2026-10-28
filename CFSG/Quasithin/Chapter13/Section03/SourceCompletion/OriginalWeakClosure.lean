module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalModule
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalFusion

/-!
# Original unitary weak closure with point geometry discharged

For the same original F.9 data, the normal natural-six component and
chosen Sylow flag construct the abelian point closure. Its literal
normalizer fusion and the completed binary G₂ fixed-space-family theorem
then prove 13.3.19(1–2). No transitivity, closure, coordinate placement,
parabolic-image, hyperplane or fixed-space classification premise remains.

The earlier normal-module and ambient source hypotheses are retained for
13.3.2/17's producers. This is the actual source chain through13.3.19(2),
not the still upstream terminal12.2.11(c)/E.1.11 implications.
Source: Aschbacher–Smith 13.3.18–19, printed pp.894–896.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] [Finite G]

/-- The literal original module has abelian point closure, commuting
intersecting conjugates, and weak closure centralizing the module. -/
theorem unitary_weakClosure_of_original_module
    (D:ChapterF.Section09.Setup G) (M:Subgroup G)
    [IsElementaryAbelian 2 D.V]
    (e:inducedAutomizer D.V D.L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0:Additive D.V≃ₗ[F]Atlas.G2.Natural.Space F)
    (he0:∀(l:inducedAutomizer D.V D.L) v,E0 (automizerRepresentation D.V l v)=
      Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV:D.Vplus≤D.V) (hZV:D.V₁≤D.V)
    (hTZ:(D.T:Subgroup G)≤normalizer (D.V₁:Set G))
    (hTU:(D.T:Subgroup G)≤normalizer (D.Vplus:Set G))
    (hZ:Nat.card D.V₁=2) (hU:Nat.card D.Vplus=8)
    (hres:pResidual 2 D.L=⊤)
    (hTL:(D.T:Subgroup G)≤normalizer (D.L:Set G))
    (hcharL:generalizedFitting D.L=pCore 2 D.L)
    (hVLT:D.V≤D.LT) (hred:IsPReduced 2 (D.V.subgroupOf D.LT))
    (hsyl:(D.T:Subgroup G)⊓centralizer (D.V:Set G)=D.LT.pCoreIn 2)
    (hcharH:generalizedFitting D.H=pCore 2 D.H)
    (hcontrol:D.H⊓normalizer (D.Vplus:Set G)≤normalizer (D.V:Set G))
    (hNL:normalizer (D.V:Set G)≤normalizer (D.L:Set G))
    (hfaith:D.L⊓centralizer (D.V:Set G)≤D.L.pCoreIn 2)
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→D.LT≤N→N=M)
    (hout:¬D.H≤M)
    (hcomm:∀g∈D.H,⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆≤
      D.V⊓D.V.map (MulAut.conj g).toMonoidHom →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥)
    (B:Subgroup G) (hBV:B≤D.V)
    (hTB:(D.T:Subgroup G)≤normalizer (B:Set G)) (hB:Nat.card B=4)
    (hr:(3:ℕ∞)<globalR D.V) (hHfull:D.H=normalizer (D.V₁:Set G))
    (hm:⁅D.QH,B⁆≠⊥) :
    IsMulCommutative D.VH ∧
    (∀g:G,D.V⊓D.V.map (MulAut.conj g).toMonoidHom≠⊥→
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥) ∧
    indexedWeakClosure D.V (D.T:Subgroup G) 2≤centralizer (D.V:Set G) := by
  have hc : IsMulCommutative D.VH :=unitary_closure_abelian_of_original_module D M e E0 he0 hUV hZV hTZ hTU
    hZ hU hres hTL hcharL hVLT hred hsyl hcharH hcontrol hNL hfaith hu hout hcomm
    B hBV hTB hB hr hHfull hm
  have : IsMulCommutative (conjugateSpanBy D.V D.H) := hc
  have hTN:(D.T:Subgroup G)≤normalizer (D.V:Set G):=
    le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer hVLT).mp hred.normal)
  have hLN:D.L≤normalizer (D.V:Set G):=
    le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer hVLT).mp hred.normal)
  refine ⟨hc,?_,?_⟩
  · exact fun g=>unitary_intersecting_conjugates_commute D.L D.V₁ D.H
      hZV hZ hHfull e E0 he0 g
  · exact unitary_weakClosure_of_point_closure (D.T:Subgroup G) D.L D.V₁ D.H
      hZV hZ hHfull hTN hLN hNL e E0 he0 hr

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
