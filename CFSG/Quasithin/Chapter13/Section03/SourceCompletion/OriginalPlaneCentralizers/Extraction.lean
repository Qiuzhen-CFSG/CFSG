module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Extraction.CubicResidual
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.ThreeFreeFullSylow

/-!
# Complete extraction for the original nondegenerate plane

The marked-module geometry gives the actual C.2.3 setup and an escaping
relative C-component. If Q moves it, the second cubic and the original
component-residual theorem force its two-core quotient to be three-free.
Its full Sylow intersection then makes Q Sylow in JQ. The C.1.29 ordered
block theorem puts this three-free join inside the control group, contradicting
escape. Thus Q normalizes an escaping component, and the earlier Sylow
repositioning constructs all fields of LocalData.

This proves LocalExtraction from the original Context. Inspection and the
linear-three chief-factor contradiction are separate remaining arguments.
Source: Aschbacher--Smith 13.3.12, printed p.889; C.2.4(1--2), p.144.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- The remaining three-free full-Sylow component cannot escape the original
local control group. The Sylow is transported through the actual inclusion. -/
theorem Context.three_free_full_sylow_component_le
    (s : Context T L V) (d : MarkedPlane V) {J : Subgroup G}
    (hJ : J ∈ Chapter1.cComponentsIn (centralizer (d.A : Set G)))
    [IsQuasisimple (J ⧸ pCore 2 J)]
    (hthree : ¬ 3 ∣ Nat.card (J ⧸ pCore 2 J))
    (S : Sylow 2 J)
    (hS : (S : Subgroup J).map J.subtype ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    J ≤ centralizer (d.A : Set G) ⊓ normalizer (L : Set G) := by
  let H := centralizer (d.A : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let J₀ := J.subgroupOf H
  let Q₀ := Q.subgroupOf H
  let M₀ := (H ⊓ normalizer (L : Set G)).subgroupOf H
  let e : J₀ ≃* J := subgroupOfEquivOfLe hJ.1
  let eQ := QuotientGroup.congr (pCore 2 J₀) (pCore 2 J) e (pCore_map_iso 2 e)
  let : IsQuasisimple (J₀ ⧸ pCore 2 J₀) := IsQuasisimple.of_mulEquiv eQ.symm
  let S₀ : Sylow 2 J₀ := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hS₀ : (S₀ : Subgroup J₀).map J₀.subtype ≤ Q₀ := by
    rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
    exact hS (mem_map_of_mem J.subtype hy)
  have hr := s.core_plane_radical d
  have hc : pCore 2 H ≤ Q₀ := pCore_le_of_pCore_normalizer_le Q₀ hr.isPGroup hr.2.le
  have hle := ChapterC.Section02Source.three_free_component_le_control_of_full_sylow
    (s.plane_local_control d).2.1 Q₀ M₀ J₀ hr.isPGroup hc
    (s.plane_local_control d).2.2.1
    (s.centralizer_characteristicTwo d.A d.le_module d.ne_bot) hJ.2
    (by rwa [Nat.card_congr eQ.toEquiv]) S₀ hS₀
  intro j hj
  exact hle (show (⟨j,hJ.1 hj⟩ : H) ∈ J₀ from hj)

/-- Original 13.3.12 extraction, with all local premises discharged from the
chosen marked module and the actual plane centralizer. -/
theorem Context.localExtraction (s : Context T L V) : LocalExtraction T L V := by
  intro d hout
  rcases s.localData_or_three_free_component d hout with h | ⟨J,hJ,hq,_,ho,_,⟨S,hS⟩,h3⟩
  · exact h
  · let := hq
    exact (ho (s.three_free_full_sylow_component_le d hJ h3 S
      (hS.le.trans inf_le_left))).elim
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
