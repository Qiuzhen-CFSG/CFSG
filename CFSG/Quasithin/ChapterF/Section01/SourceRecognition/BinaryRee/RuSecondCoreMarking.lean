module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.BinaryRee.RuFirstEndpoint
public import Theory.SpecificGroups.ReeTwo.FirstParabolicCoordinates
public import Theory.GroupTheory.UpperCentralSeriesCentralizerTransport

/-!
# The original binary Ree middle and second core

The first-endpoint identification transports the original Sylow subgroup to
`SylowModel`. The second core is intrinsic: it is the centralizer of the
second upper center of that same Sylow subgroup. Restricting the Sylow
isomorphism therefore marks both groups compatibly, with their original
inclusions. This discharges the core-identification input in the second
endpoint of GLS IV, Chapter F, Lemma 1.12, as applied in Chapter J, 4.5.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

/-- The unchanged middle has the full binary Ree Sylow multiplication. -/
theorem SourceChoice.T_F_equiv_sylowModel (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    Nonempty ((p.T_F B5)≃*ReeTwo.SylowModel) := by
  obtain ⟨e,_⟩:=s.exists_F₁_core_preserving_equiv B5 hi
  obtain ⟨P,hP⟩:=s.T_F_sylow_F₁ p B5 hi
  let Q:Sylow 2 ReeTwo.Centralizer:=P.mapSurjective (f:=e.symm.toMonoidHom) e.symm.surjective
  let f:(p.T_F B5)≃*P:=(subgroupOfEquivOfLe (p.T_F_le_F₁ B5)).symm.trans
    (MulEquiv.subgroupCongr hP.symm)
  let g:P≃*Q:=e.symm.subgroupMap P
  exact ⟨f.trans (g.trans (ReeTwo.SylowModel.equiv Q).symm)⟩

/-- A simultaneous marking of the original middle and original second core.
The two maps commute with their literal inclusions. -/
theorem SourceChoice.exists_T_F_A_marking (s:SourceChoice p)
    (B5:Sylow 5 d.toTypeRuSetup.H) (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃(eT:(p.T_F B5)≃*ReeTwo.SylowModel)
      (eA:(p.A B5)≃*ReeTwo.SylowModel.firstParabolicCore),
      ∀a:p.A B5,eT (inclusion (show p.A B5≤p.T_F B5 from le_sup_left) a)=
        (eA a:ReeTwo.SylowModel) := by
  obtain ⟨eT⟩:=s.T_F_equiv_sylowModel B5 hi
  let M:=p.T_F B5
  let A:Subgroup M:=(p.A B5).subgroupOf M
  have hAM:p.A B5≤M:=le_sup_left
  have hAI:A=centralizer (Subgroup.upperCentralSeries M 2:Set M):=by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le hAM,s.T_F_intrinsic_A B5 hi]
  have hmap:A.map eT.toMonoidHom=ReeTwo.SylowModel.firstParabolicCore:=by
    rw [hAI,Subgroup.map_centralizer_upperCentralSeries]
    rfl
  let eA:(p.A B5)≃*ReeTwo.SylowModel.firstParabolicCore:=
    (subgroupOfEquivOfLe hAM).symm.trans ((eT.subgroupMap A).trans (MulEquiv.subgroupCongr hmap))
  exact ⟨eT,eA,fun _=>rfl⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
