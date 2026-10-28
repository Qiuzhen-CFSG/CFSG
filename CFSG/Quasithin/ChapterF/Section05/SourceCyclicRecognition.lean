module
public import CFSG.Quasithin.ChapterF.Section05.SourceRootRecognition
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerCyclicRoot
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerLocalComplement
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.GraphCentralizerEndpointPair

/-!
# F.5 ambient recognition reduced to the elementary R₀ exclusion

The source centralizer has already been proved to be R D, and the literal
fixed-endpoint involution pair is constructed. A non-elementary R₀ of order
four supplies a generator squaring to the graph involution. This generator
lies in H and centralizes both the graph residual and the actual corrected
plane complement. The full marked-amalgam consumer then identifies the
ambient group as PSL₄(3).

Only the independent elementary-pair contradiction remains explicit here;
no model recognition, compatibility, fusion or centralizer premise is added.
Source: Aschbacher–Smith F.5.5–8, printed pp.301–304.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05
open Subgroup Theory.GroupTheory GreenBook.LieModels.UnitaryFour
open ExceptionalLocal
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
  (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
  (R : Sylow 2 (C c i)) (hR : Tf c i ≤ (R : Subgroup (C c i)))
include h hR

theorem source_centralizer_root_data_of_not_elementary
    (hnot : ¬ IsElementaryAbelian 2 (Rzero c i R)) :
    ∃r:G,r∈H c i ∧ r^2=Source.graphElement c i ∧
      (∀a∈sourceLocalComplement c i,r*a=a*r) ∧
      (∀a∈(pResidual 2 (C c i)).map (C c i).subtype,r*a=a*r) := by
  obtain ⟨r,hr,_,hsq⟩:=source_Rzero_square_root_of_not_elementary c i z h R hR hnot
  refine ⟨r,source_R_le_H c i z h R hR hr.1,hsq,
    source_Rzero_commutes_localComplement c i z h R hR r hr,?_⟩
  rw [Rzero,source_DtwoResidual_eq_centralizer_residual c i z h R hR] at hr
  exact fun a ha=>(hr.2 a ha).symm

theorem source_ambient_of_Rzero_not_elementary
    (hnot : ¬ IsElementaryAbelian 2 (Rzero c i R)) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)) := by
  obtain ⟨r,hr,hsq,hc,hres⟩:=source_centralizer_root_data_of_not_elementary c i z h R hR hnot
  obtain ⟨s,t,hs,ht,hsout,htout,hs2,ht2,hst⟩:=source_fixed_endpoint_pair c i z h
  exact source_ambient_of_fixed_endpoints_and_root c i z h R hR
    (source_centralizer_join c i z h R hR) r hr hsq hc hres
    s t hs ht hsout htout hs2 ht2 hst

end CFSG.Quasithin.ChapterF.Section05
