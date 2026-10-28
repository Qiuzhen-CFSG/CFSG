module

public import CFSG.Quasithin.ChapterJ.Section04To05.SecondParabolic.Structure
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.SecondCore

/-!
# The marked model endpoints belong to the original second core A

The canonical model words are first lifted into the actual second endpoint.
Every supplied endpoint equivalence carries its intrinsic two-core onto the
intrinsic two-core of the original F₂. The earlier J.4 quotient calculation
identifies that image with the original A. This transports the two long-root
endpoints and their short-root commutator with the literal endpoint map;
no arbitrary core-membership premise or completion equivalence is used.
Source: Aschbacher--Smith J.4.5 and the proof of J.4.7, printed pp.442,444.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedSecondCore
open Subgroup
open Tits.ExceptionalParabolics.FullRee
open Tits.ExceptionalParabolics.FullRee.LongRootPaths

/-- Inclusion of the actual left endpoint in the model second parabolic. -/
def modelLeft : second := ⟨leftSix,map_subtype_le _ leftSix_mem_secondCore⟩

/-- Inclusion of the actual right endpoint in the same model parabolic. -/
def modelRight : second := ⟨u,map_subtype_le _ u_mem_secondCore⟩

/-- Inclusion of their actual short-root commutator. -/
def modelShort : second := ⟨shortCommutator,map_subtype_le _ shortCommutator_mem_secondCore⟩

private theorem left_mem : modelLeft∈pCore 2 second :=
  (mem_map_iff_mem second.subtype_injective).mp leftSix_mem_secondCore
private theorem right_mem : modelRight∈pCore 2 second :=
  (mem_map_iff_mem second.subtype_injective).mp u_mem_secondCore
private theorem short_mem : modelShort∈pCore 2 second :=
  (mem_map_iff_mem second.subtype_injective).mp shortCommutator_mem_secondCore

variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)
  (B5 : Sylow 5 d.toTypeRuSetup.H) (X : Sylow 3 p.parabolic)
  (h : Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3)))
  (e : second ≃* p.F₂ B5 X)

include h in
/-- The literal endpoint equivalence sends the marked two endpoints and
commutator into the original A constructed before recognition. -/
theorem source_endpoints_mem_A :
    (e modelLeft : G)∈p.A B5 ∧ (e modelRight : G)∈p.A B5 ∧
      (e modelShort : G)∈p.A B5 := by
  have hm (x : second) (hx:x∈pCore 2 second) : (e x:G)∈p.A B5 := by
    have he : e x∈pCore 2 (p.F₂ B5 X) := pCore_map_iso 2 e ▸ mem_map_of_mem e.toMonoidHom hx
    rw [p.F₂_core B5 X h] at he
    exact he
  exact ⟨hm modelLeft left_mem,hm modelRight right_mem,hm modelShort short_mem⟩

/-- The source commutator formula retains the same endpoint map. -/
theorem source_commutator :
    (e modelLeft:G)*(e modelRight:G)*(e modelLeft:G)⁻¹*(e modelRight:G)⁻¹ = (e modelShort:G) := by
  have hm : modelLeft*modelRight*modelLeft⁻¹*modelRight⁻¹=modelShort :=
    Subtype.ext commutator_eq_short
  exact (by simpa only [map_mul,map_inv,coe_mul,coe_inv] using
    congrArg (fun a : p.F₂ B5 X => (a:G)) (congrArg e hm))

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedSecondCore
