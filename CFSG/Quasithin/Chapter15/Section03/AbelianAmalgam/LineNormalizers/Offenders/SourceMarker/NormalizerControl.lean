module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceMarker.Definitions
public import Theory.GroupTheory.ElementaryThompsonFrattini

/-!
# Lifting the normalizer of the literal marked Thompson image

The preimage of q(J(S_E)) is J(S_E) O₂(H). It lies between J(S_E) and S_E,
so it has the same elementary Thompson subgroup. A normalizer of that
preimage therefore normalizes J(S_E). Maximum-family containment also gives
J(S_E) = J(T_E), allowing the original normalizer control to put the lift in M.
The core is the full temporary core; it is never identified with original Q_E.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 15.3.67, printed pp.1153–1154 (PDF pp.1170–1171).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceMarker
open Replacement Replacement.Transvections BestReduction.FullCoreTransfer BestReduction.SourceAssembly
variable {G : Type*} [Group G] [Finite G]
  {Y T V M E Pc : Subgroup G} [IsMulCommutative V]
  (o : Geometry.OriginalData Y T V M E Pc)
local notation "H" => temporaryLineNormalizer T V E
local notation "Q" => localCore T V E
local notation "S" => centralizerSylow T V E
local notation "J" => elementaryAbelianMaxJ S
local notation "q" => QuotientGroup.mk' Q
local notation "I" => thompsonImage T V E

include o in
/-- The full temporary core lies in the unchanged S_E. -/
private theorem core_le_centralizerSylow : Q ≤ S := by
  have hQT := temporaryCore_le_lineT T V E o.line_le o.sylow o.sylow_image
  have hHQ : H ≤ normalizer (temporaryCore T V E : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (temporaryCore_le T V E)).mp
      (temporaryCore_normal T V E)
  have hQ : temporaryCore T V E ≤ T ⊓ centralizer (E : Set G) :=
    (le_pCoreIn_of_normalizes (temporaryCore_isPGroup T V E)
      (hQT.trans le_sup_right)
      ((sup_le o.inherited.2.1 (lineT_le_temporary T V E o.line_le)).trans hHQ)).trans o.local_core
  exact fun _ hx => hQ hx

include o in
/-- The actual maximum-family containment identifies J(S_E) with J(T_E). -/
private theorem sylow_thompson_map
    (hJ : elementaryAbelianMaxJ (lineT T E) ≤ centralizer (E : Set G)) :
    (J).map (H).subtype = elementaryAbelianMaxJ (lineT T E) := by
  have hST : T ⊓ centralizer (E : Set G) ≤ lineT T E :=
    le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  rw [← elementaryAbelianMaxJ_map_injective _ (H).subtype_injective,
    map_subgroupOf_eq_of_le (hST.trans (lineT_le_temporary T V E o.line_le))]
  exact elementaryAbelianMaxJ_eq_of_intermediate _ _
    (le_inf ((sSup_le fun _ hA => hA.1).trans inf_le_left) hJ) hST

include o in
/-- The literal marked Thompson image belongs to the identical temporary actor. -/
theorem marked_map_le_actor : (J).map q ≤ I := by
  apply map_mono
  exact sSup_le fun A hA => le_sSup (SourceSylow.maximum_comparison o A hA)

include o in
/-- Every lift normalizing q(J(S_E)) lies in M by the original Thompson normalizer bound. -/
theorem normalizer_lift_mem_M
    (hJ : elementaryAbelianMaxJ (lineT T E) ≤ centralizer (E : Set G))
    (hNJ : normalizer (elementaryAbelianMaxJ (lineT T E) : Set G) ≤ M)
    (x : H) (hx : q x ∈ normalizer ((J).map q : Set (H ⧸ Q))) : x.val ∈ M := by
  have hn : x ∈ normalizer (((J).map q).comap q : Set H) :=
    ((J).map q).le_normalizer_comap q hx
  rw [comap_map_eq, QuotientGroup.ker_mk'] at hn
  have hB : elementaryAbelianMaxJ (J ⊔ Q) = J :=
    elementaryAbelianMaxJ_eq_of_intermediate S (J ⊔ Q) le_sup_left
      (sup_le (sSup_le fun _ hA => hA.1) (core_le_centralizerSylow o))
  have hnJ : x ∈ normalizer (J : Set H) := by
    rw [mem_normalizer_iff_map_conj_eq] at hn ⊢
    rw [← hB]
    exact (elementaryAbelianMaxJ_map_equiv (MulAut.conj x) (J ⊔ Q)).symm.trans
      (congrArg elementaryAbelianMaxJ hn)
  apply hNJ
  have hh := (J).le_normalizer_map (H).subtype (mem_map_of_mem (H).subtype hnJ)
  rwa [sylow_thompson_map o hJ] at hh

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceMarker
