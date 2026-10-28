module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.Span
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Thompson movement survives an actual section containing the chosen module

Let a local overgroup N preserve E ≤ V ≤ H, with V the original prepared
module. Its kernel on H/E normalizes V, so maximal-local control puts that
kernel in M. If the original Sylow Thompson subgroup were in the kernel,
the Thompson Frattini argument would put N in M. Thus an actual outside
overgroup still has Thompson movement on this particular section.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original Sylow Thompson subgroup moves H/E whenever E≤V≤H is
preserved by an overgroup outside the selected maximal local. -/
theorem PreparedChosenModule.section_thompson_movement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V N H E : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (hTN : (T : Subgroup G) ≤ N) (hout : ¬ N ≤ M)
    (hNH : N ≤ normalizer (H : Set G)) (hNE : N ≤ normalizer (E : Set G))
    (hEV : E ≤ V) (hVH : V ≤ H) :
    ¬ ⁅elementaryAbelianMaxJ (T : Subgroup G),H⁆ ≤ E := by
  let K := commutatorPreimage N H E
  have hNK : N ≤ normalizer (K : Set G) :=
    commutatorPreimage_normalized N H E N hNE N.le_normalizer hNH hNE
  have hKV : ⁅K,V⁆ ≤ V :=
    ((commutator_mono le_rfl hVH).trans
      (commutator_commutatorPreimage_le N H E hNE)).trans hEV
  have hKM : K ≤ M := by
    have hKn : K ≤ normalizer (V : Set G) := by
      apply le_normalizer_iff_commutator_le_right.mpr
      exact hKV
    let := h.elementary
    exact hKn.trans (hM.1.1.2
      ⟨V,h.nontrivial,IsElementaryAbelian.isPGroup 2 V,rfl⟩ h.normalized)
  intro hmove
  have hTJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ N :=
    (sSup_le fun _ hA => hA.1).trans hTN
  have hm : (((T.subtype hTN : Sylow 2 N) : Subgroup N).map N.subtype) =
      (T : Subgroup G) := map_subgroupOf_eq_of_le hTN
  apply hout
  apply le_of_thompson_normalizer_control N M K (T.subtype hTN) hNK hKM
  · simpa only [hm] using le_commutatorPreimage hTJ hmove
  · simpa only [hm] using (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1

end CFSG.Quasithin.Chapter15.Section01
