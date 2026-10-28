module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.PointPlaneCore
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.ConjugateHyperplanes
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.PlaneBounds

/-!
# The unitary abelian closure from the original point and plane actions

In the contrary branch, the genuine F.9 setup and marked natural action
identify V∩Q_H with V₅. The original plane action and 13.3.15 core bound put
V in O₂(G₂). A Baer–Suzuki pair with an internal conjugator cannot move V₃
from either conjugate hyperplane, by the actual moving-plane contradiction.
The invariant pairing gives both cross-displacement bounds. Layer exchange
then bounds the induced action rank by two, contradicting r(G,V)>3.

The public source application discharges the hyperplane, movement,
cross-centralization, displacement and plane-core premises. It retains
only genuine F.9 applicability, the earlier natural point/plane marking,
13.3.17 rank/intersection/noncentrality and the actual cubic parabolic
inputs to 13.3.15. The upstream source assembly must construct those;
this is not a claim that the full original Theorem 13.3.16 is closed.

Source: Aschbacher–Smith, Lemma 13.3.18(2), printed pp.894–895.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative
open Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] [Finite G]

/-- The literal natural-six point and plane action complete the
cross-displacement and layer-exchange argument for the original closure. -/
theorem source_closure_abelian_of_plane_core
    {D:ChapterF.Section09.Setup G} (h:D.Hypothesis) :
    let :=h.elementary
    ∀ (rho:Automizer D.V→*Atlas.G2.Model F) (E:Additive D.V≃ₗ[F]W),
    (∀a v,E (automizerRepresentation D.V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v)) →
    ∀B:Subgroup G, B≤D.V →
    pointCoordinateSubspace E D.Vplus=seed →
    pointCoordinateSubspace E B=plane →
    (inducedAutomizer D.V (D.T:Subgroup G)).map rho≤Atlas.G2.unipotent →
    Atlas.G2.BinaryParabolicPair.derivedSecondAmbient≤
      (inducedAutomizer D.V (D.L₁⊔(D.T:Subgroup G))).map rho →
    (∀g∈D.H,⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆≤
      D.V⊓D.V.map (MulAut.conj g).toMonoidHom →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥) →
    ¬D.Vplus≤centralizer (D.QH:Set G) →
    (3:ℕ∞)<globalR D.V →
    (pointCoordinateSubspace E (D.V⊓D.QH)=hyperplane →
      D.V≤(normalizer (B:Set G)).pCoreIn 2) →
    IsMulCommutative D.VH := by
  let :=h.elementary
  dsimp only
  intro rho E he B hBV hs hp hT hP hcomm hncentral hr hcore
  by_contra hnonabelian
  obtain ⟨hhyper,hcor⟩:=source_point_hyperplane h rho E he hs hT hP hcomm hnonabelian hncentral
  have hVK:=hcore hhyper
  obtain ⟨g,hg,hin,hnot⟩:=exists_non_two_pair_of_nonabelian_closure h hcomm hnonabelian
  have hcent (k:G) (hk:k∈D.H)
      (hkin:k∈D.V⊔D.V.map (MulAut.conj k).toMonoidHom)
      (hknot:¬IsPGroup 2 (D.V⊔D.V.map (MulAut.conj k).toMonoidHom:Subgroup G)) :
      ⁅D.V,(D.V⊓D.QH).map (MulAut.conj k).toMonoidHom⁆≤D.Vplus := by
    have hc:=source_cross_hyperplane_centralizes_seed h rho E he B hBV hs hp hhyper hT hP hVK
      k hk hkin hknot
    have hQ:D.QH.map (MulAut.conj k).toMonoidHom=D.QH:=mem_normalizer_iff_map_conj_eq.mp
      (ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D:=D) hk)
    apply commutator_le_seed_of_point_centralizer D.V D.Vplus _ rho E he hs _ hc
    exact ((map_mono inf_le_right).trans_eq hQ).trans (h.QH_le_T.trans h.T_normalizes_V)
  have hforward:=hcent g hg hin hnot
  have hi:=internal_pair_inverse_eq D.V g hin
  have hback:=hcent g⁻¹ (D.H.inv_mem hg)
    (hi.symm ▸ (D.V⊔D.V.map (MulAut.conj g).toMonoidHom).inv_mem hin)
    (hi.symm ▸ hnot)
  have hcancel (A:Subgroup G):
      (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom=A := by
    rw [map_map]
    have hh:(MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom=MonoidHom.id G := by
      ext x;simp [MulAut.conj_apply,mul_assoc]
    rw [hh,map_id]
  have hbackward:⁅D.V.map (MulAut.conj g).toMonoidHom,D.V⊓D.QH⁆≤
      D.Vplus.map (MulAut.conj g).toMonoidHom := by
    have hh:=map_mono (f:=(MulAut.conj g).toMonoidHom) hback
    rw [map_commutator,hcancel] at hh
    exact hh
  have hcard:Nat.card D.Vplus=8 := by
    rw [←card_pointCoordinateSubspace E D.Vplus h.plus_le,hs,card_seed]
  exact hnot (source_pair_isTwo_of_cross_displacements h g hg hin hcard (hcor.le) hr hforward hbackward)

open scoped IsKleinFour
/-- The original unitary F.9 closure is abelian. Both hyperplane bounds,
both cross-displacements, and the plane-core containment are proved from
the original point/plane action and the earlier noncentrality theorem. -/
theorem source_closure_abelian_of_point_plane_actions
    {D:ChapterF.Section09.Setup G} (h:D.Hypothesis) :
    let :=h.elementary
    ∀ (rho:Automizer D.V→*Atlas.G2.Model F) (E:Additive D.V≃ₗ[F]W),
    (∀a v,E (automizerRepresentation D.V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v)) →
    ∀ (B X:Subgroup G), ∀ [IsKleinFour B], B≤D.V → D.V₁≤B →
    pointCoordinateSubspace E D.Vplus=seed →
    pointCoordinateSubspace E B=plane →
    (inducedAutomizer D.V (D.T:Subgroup G)).map rho≤Atlas.G2.unipotent →
    Atlas.G2.BinaryParabolicPair.derivedSecondAmbient≤
      (inducedAutomizer D.V (D.L₁⊔(D.T:Subgroup G))).map rho →
    Atlas.G2.BinaryParabolicPair.derivedFirstAmbient≤(inducedAutomizer D.V X).map rho →
    (∀g∈D.H,⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆≤
      D.V⊓D.V.map (MulAut.conj g).toMonoidHom →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥) →
    (3:ℕ∞)<globalR D.V →
    D.H=normalizer (D.V₁:Set G) →
    (D.T:Subgroup G)≤normalizer (B:Set G) →
    X≤normalizer (B:Set G) → (D.T:Subgroup G)≤normalizer (X:Set G) →
    IsPPerfect 2 X →
    Nat.card ((X.subgroupOf (normalizer (B:Set G))).map
      (Chapter13.Section05.AmbientSource.planeAction B))=3 →
    IsPGroup 2 (X⊓centralizer (B:Set G):Subgroup G) →
    ⁅D.QH,B⁆≠⊥ → IsMulCommutative D.VH := by
  let :=h.elementary
  dsimp only
  intro rho E he B X _ hBV hPB hs hp hT hP hXimage hcomm hr hH hTB hXB hTX hX hx hkX hm
  have hBp:B≤D.Vplus := by
    intro b hb
    let v:Additive D.V:=Additive.ofMul ⟨b,hBV hb⟩
    have hw:E v∈seed := by
      have hplane:plane≤seed := plane_le_seed
      exact hplane (hp ▸ (mem_pointCoordinateSubspace E B v).mpr hb)
    exact (mem_pointCoordinateSubspace E D.Vplus v).mp (hs.symm ▸ hw)
  have hnoncentral:¬D.Vplus≤centralizer (D.QH:Set G) := by
    intro hc
    apply hm
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hBp.trans hc)
  apply source_closure_abelian_of_plane_core h rho E he B hBV hs hp hT hP hcomm hnoncentral hr
  intro hc
  have hQ:D.QH=(normalizer (D.V₁:Set G)).pCoreIn 2 := congrArg (fun K:Subgroup G=>K.pCoreIn 2) hH
  obtain ⟨hbound,hcore⟩:=Chapter13.Section05.AmbientSource.point_core_centralizer_le_plane_cores
    D.T D.V₁ B X h.point_card hPB h.normalizes_point hTB hXB hTX hX hx hkX (hQ ▸ hm)
  apply source_module_le_plane_core B (D.V⊓D.QH) D.QH X rho E he hBV inf_le_left inf_le_right
    hc hXB hXimage
  rw [hQ]
  exact hbound.trans hcore

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
