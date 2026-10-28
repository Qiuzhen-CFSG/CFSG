module
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.Splitting.Source
public import CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup.SourceCores
public import CFSG.Quasithin.Chapter13.Section09.TerminalObstruction
public import CFSG.Quasithin.Chapter13.Section09.NormalizerStructure.Fusion
/-!
# The terminal subgroup from the original wreath source hypotheses

The actual marked S4 factor from 13.9.10 discharges every placement, generation,
order and internal-fusion input. Thus H = O²(C_G(E)) is PSL3(2), centralized by
M1. Its nonsolvability and solvability of C_G(z) exclude z-conjugates in M1.
Consequently the unordered four-point fusion result takes the reversed branch.
This theorem records that remaining branch; it does not assert the full 13.9.1
exclusion or reuse the incorrect printed Delta5 multiplication claim.

Source: Aschbacher--Smith, 13.9.10 and the final paragraph of 13.9.1,
printed pp.973--974. The unresolved step is exclusion of this reversed branch.
-/
public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath TerminalSubgroup
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

/-- The literal terminal residual is PSL3(2), centralized by the original
first S4 factor, using only the original QTKE and wreath configuration. -/
theorem source_terminal_psl3Two {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    Nonempty (terminal m.terminalFour≃*Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∧
      m.factor 1≤centralizer (terminal m.terminalFour:Set G) := by
  obtain ⟨X,eX,hX,hVJ,hVB,hz⟩:=m.exists_terminal_symmetric_factor hG
  exact m.terminal_psl3Two_of_marked_symmetric_core hG X eX hX hVJ hVB hz

/-- Solvability of the original z-centralizer forbids its conjugates in the
first S4 factor once the actual terminal residual has been constructed. -/
theorem terminal_factor_not_fused_z {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (x:G) (hx:x∈m.factor 1) : ¬IsConj m.z x := by
  obtain ⟨⟨eH⟩,hcomm⟩:=m.source_terminal_psl3Two hG
  apply Theory.GroupTheory.not_isConj_of_nonsolvable_subgroup_centralized
    (terminal m.terminalFour) (m.marked_centralizer_z_solvable (hG.evenCharacteristic d.T)) ?_ (hcomm hx)
  intro hs
  let := hs
  exact not_isSolvable_psl3_two
    (Group.isSolvable_of_surjective (f:=eH.toMonoidHom) eH.surjective)

/-- The checked terminal argument forces the reversed local four-point
alternative. This records the exact remaining branch instead of assuming
the printed, incorrect Delta5 product assertion. -/
theorem terminal_reversed_fusion {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    m.fusionFlags 2=false ∧ m.fusionFlags 4=true := by
  have hn:m.fusionFlags 2=false := by
    simp only [fusionFlags,decide_eq_false_iff_not]
    apply m.terminal_factor_not_fused_z hG
    change m.embedding (SymmetricFourWreath.factor 1 (square (DihedralGroup.sr 0)))∈m.factor 1
    exact mem_map_of_mem m.embedding ⟨square (DihedralGroup.sr 0),rfl⟩
  exact (m.normalizerOrbit_fusion_alternatives hG).resolve_left (fun h=>by rw [hn] at h;cases h.1)
end CFSG.Quasithin.Chapter13.Section09.Marking
