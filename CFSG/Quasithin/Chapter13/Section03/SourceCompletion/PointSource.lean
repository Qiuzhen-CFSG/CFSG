module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.ComponentPerfect
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.FlagNormalization

/-!
# The original unitary point-centralizer closure

From a compatible natural-six marking of the original chosen module, this
consumer constructs F.9.1 and proves its closure V_H abelian. The original
component's perfection, point/plane cardinalities and incidence, local and
Sylow flag normalization, point-parabolic coverage, and the plane residual's
cubic image and two-group kernel are all derived. The previous point/core
argument then constructs the hyperplane and cross-displacement bounds.

The genuine earlier chosen-module normality/faithful-kernel/reducedness,
Sylow marking, uniqueness, characteristic-two, and 13.3.17 hypotheses remain.
No abelian closure, full parabolic image or extra model classification is
assumed. The full Hypothesis13.3.1 discharge remains with its source assembly.

Source: Aschbacher–Smith 13.3.18(1–2), printed pp.894–895.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative IsKleinFour
open Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] [Finite G]

/-- The original abelian-closure consumer, with F.9 applicability and all
subsequent point/hyperplane/cross-action premises discharged in one proof. -/
theorem unitary_closure_abelian_of_source_action
    (D:ChapterF.Section09.Setup G) (M:Subgroup G)
    [IsElementaryAbelian 2 D.V]
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
    (hp:pointCoordinateSubspace E B=plane)
    (hr:(3:ℕ∞)<globalR D.V) (hHfull:D.H=normalizer (D.V₁:Set G))
    (hm:⁅D.QH,B⁆≠⊥) : IsMulCommutative D.VH := by
  have hTN:(D.T:Subgroup G)≤normalizer (D.V:Set G):=
    le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer hVLT).mp hred.normal)
  have hLN:D.L≤normalizer (D.V:Set G):=
    le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer hVLT).mp hred.normal)
  let : Group.IsPerfect D.L:=component_isPerfect_of_unitary_action D.L rho E he hLN hfaith hres hderived
  let : IsElementaryAbelian 2 B:=IsElementaryAbelian.of_le hBV
  have hBcard:Nat.card B=4:=by
    rw [←card_pointCoordinateSubspace E B hBV,hp,card_plane]
  let : Nontrivial B:=Finite.one_lt_card_iff_nontrivial.mp (by rw [hBcard];decide)
  let : IsKleinFour B:=⟨hBcard,IsElementaryAbelian.exponent_eq_prime⟩
  have hZcard:Nat.card D.V₁=2:=by
    rw [←card_pointCoordinateSubspace E D.V₁ hZV,hz,card_pointLine]
  have hTC:=sylow_centralizes_marked_point D.T D.V₁ rho E he hz hZV hTN hT
  have hH:D.H≤D.Gz:=hHfull ▸ normalizer_le_centralizer_of_card_two D.V₁ hZcard
  have hLC:D.L₁≤D.L⊓centralizer (D.V₁:Set G):=map_subtype_le _
  have hlocalC:D.L₁⊔(D.T:Subgroup G)≤centralizer (D.V₁:Set G):=
    sup_le (hLC.trans inf_le_right) hTC
  have hlocal:D.L₁⊔(D.T:Subgroup G)≤D.H:=by
    rw [hHfull]
    exact hlocalC.trans (Subgroup.centralizer_le_normalizer _)
  have hlocalN:=point_centralizer_normalizes_marked_seed D.Vplus D.V₁
    (D.L₁⊔(D.T:Subgroup G)) rho E he hs hz hUV
    (sup_le ((hLC.trans inf_le_left).trans hLN) hTN) hlocalC
  have hTB:=sylow_normalizes_marked_plane D.T B rho E he hp hBV hTN hT
  have hPB:=marked_point_le_plane D.V₁ B E hz hp hZV
  let K:=D.L⊓normalizer (B:Set G)
  let X:Subgroup G:=(pResidual 2 K).map K.subtype
  have hXK:X≤K:=map_subtype_le _
  have hXimage:=source_plane_residual_cubic D.L B rho E he hp hBV hLN hderived
  have hx:=source_plane_action_card_three B X rho E he hp
    (hXK.trans inf_le_right) (isPPerfect_embedded_pResidual 2 K) hXimage
  have hkX:IsPGroup 2 (X⊓centralizer (B:Set G):Subgroup G):=
    (source_plane_centralizer_isTwo D.L B rho E he hp hLN hfaith).to_le
      (inf_le_inf (hXK.trans inf_le_left) le_rfl)
  exact unitary_closure_abelian_of_component_action D M rho E he hs hz hUV hZV hT hderived
    hres hTL hcharL hVLT hred hsyl hH hlocal hcharH hlocalN hcontrol hNL hfaith hu hout
    hcomm B hBV hPB hp hr hHfull hTB hx hkX hm

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
