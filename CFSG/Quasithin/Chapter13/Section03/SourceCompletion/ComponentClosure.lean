module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.CubicClosure

/-!
# Applying the actual component's parabolic lifts to the unitary closure

The original component action contains the marked derived binary G₂ group.
This supplies the point parabolic through L₁T and the plane cubic through
O²(N_L(V₂)), in the same natural-module frame. The latter residual's
normalization and two-perfectness are constructed here. Thus no full
plane-parabolic image assumption enters the closure argument.

The remaining earlier inputs are the chosen-module source properties,
13.3.17, and the cubic image and two-group kernel of the plane residual.
Source: Aschbacher–Smith 13.3.18, printed pp.894–895.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative IsKleinFour
open Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] [Finite G]

/-- The original abelian-closure consumer, with F.9 applicability and all
subsequent point/hyperplane/cross-action premises discharged in one proof. -/
theorem unitary_closure_abelian_of_component_action
    (D:ChapterF.Section09.Setup G) (M:Subgroup G)
    [IsElementaryAbelian 2 D.V] [Group.IsPerfect D.L]
    (rho:Automizer D.V→*Atlas.G2.Model F) (E:Additive D.V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation D.V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hs:pointCoordinateSubspace E D.Vplus=seed)
    (hz:pointCoordinateSubspace E D.V₁=pointLine)
    (hUV:D.Vplus≤D.V) (hZV:D.V₁≤D.V)
    (hT:(inducedAutomizer D.V (D.T:Subgroup G)).map rho≤Atlas.G2.unipotent)
    (hderived:commutator (Atlas.G2.Model F)≤(inducedAutomizer D.V D.L).map rho)
    (hres:pResidual 2 D.L=⊤)
    (hTL:(D.T:Subgroup G)≤normalizer (D.L:Set G))
    (hcharL:generalizedFitting D.L=pCore 2 D.L)
    (hVLT:D.V≤D.LT) (hred:IsPReduced 2 (D.V.subgroupOf D.LT))
    (hsyl:(D.T:Subgroup G)⊓centralizer (D.V:Set G)=D.LT.pCoreIn 2)
    (hH:D.H≤D.Gz) (hlocal:D.L₁⊔(D.T:Subgroup G)≤D.H)
    (hcharH:generalizedFitting D.H=pCore 2 D.H)
    (hlocalN:D.L₁⊔(D.T:Subgroup G)≤normalizer (D.Vplus:Set G))
    (hcontrol:D.H⊓normalizer (D.Vplus:Set G)≤normalizer (D.V:Set G))
    (hNL:normalizer (D.V:Set G)≤normalizer (D.L:Set G))
    (hfaith:D.L⊓centralizer (D.V:Set G)≤D.L.pCoreIn 2)
    (hu:∀N:Subgroup G,IsMaximalTwoLocal N→D.LT≤N→N=M)
    (hout:¬D.H≤M)
    (hcomm:∀g∈D.H,⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆≤
      D.V⊓D.V.map (MulAut.conj g).toMonoidHom →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥)
    (B:Subgroup G) [IsKleinFour B] (hBV:B≤D.V) (hPB:D.V₁≤B)
    (hp:pointCoordinateSubspace E B=plane)
    (hr:(3:ℕ∞)<globalR D.V) (hHfull:D.H=normalizer (D.V₁:Set G))
    (hTB:(D.T:Subgroup G)≤normalizer (B:Set G))
    (hx:Nat.card ((((pResidual 2 (D.L⊓normalizer (B:Set G):Subgroup G)).map
        (D.L⊓normalizer (B:Set G)).subtype).subgroupOf (normalizer (B:Set G))).map
      (Chapter13.Section05.AmbientSource.planeAction B))=3)
    (hkX:IsPGroup 2 (((pResidual 2 (D.L⊓normalizer (B:Set G):Subgroup G)).map
      (D.L⊓normalizer (B:Set G)).subtype)⊓centralizer (B:Set G):Subgroup G))
    (hm:⁅D.QH,B⁆≠⊥) : IsMulCommutative D.VH := by
  let K:=D.L⊓normalizer (B:Set G)
  let X:Subgroup G:=(pResidual 2 K).map K.subtype
  have hTN:(D.T:Subgroup G)≤normalizer (D.V:Set G):=
    le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer hVLT).mp hred.normal)
  have hLN:D.L≤normalizer (D.V:Set G):=
    le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer hVLT).mp hred.normal)
  have hTC:=sylow_centralizes_marked_point D.T D.V₁ rho E he hz hZV hTN hT
  have hP:=source_point_parabolic_covered D.T D.L D.V₁ rho E he hz hZV hTC hTL hderived
  have hXimage:=source_plane_residual_cubic D.L B rho E he hp hBV hLN hderived
  have hXB:X≤normalizer (B:Set G):=(map_subtype_le _).trans inf_le_right
  have hTX:(D.T:Subgroup G)≤normalizer (X:Set G):=
    ((le_inf hTL (hTB.trans (normalizer (B:Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image K (pResidual 2 K))
  have hX:IsPPerfect 2 X:=isPPerfect_embedded_pResidual 2 K
  have hD:=f9_hypothesis_of_unitary_point_action D M rho E he hs hz hUV hZV hT hP
    hres hTL hcharL hVLT hred hsyl hH hlocal hcharH hlocalN hcontrol hNL hfaith hu hout hcomm
  exact source_closure_abelian_of_point_plane_cubic hD rho E he B X hBV hPB hs hp hT hP
    hXimage hcomm hr hHfull hTB hXB hTX hX hx hkX hm

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
