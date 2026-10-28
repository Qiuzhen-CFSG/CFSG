module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.Products
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.ElementaryAbelianMaxOrder

/-!
# The original Thompson subgroup survives the two-core quotient

If the elementary Thompson subgroup of a Sylow two-subgroup lies in a
normal subgroup, the same holds for the Thompson subgroup of any overgroup
of its generators. The proof conjugates each maximum elementary subgroup
into the Sylow subgroup and compares maximum orders; it does not assume
monotonicity of the Thompson construction.

Apply this to the original `I = J(C_G(E))`. The recognized index of `I₀`
forces `I` outside `M_E`, whereas the original `Q_E` is in `T_E ≤ M_E`.
Consequently `J(T_E) = J(R)` has nonidentity image modulo `Q_E`. This is
the nontrivial Thompson input for the second quotient factor and the
commutator in 15.3.67, without a temporary-core identification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Lemma 15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped Pointwise

private theorem maxJ_le_normal_of_sylow
    {H : Type*} [Group H] [Finite H] (P : Sylow 2 H) (C N : Subgroup H) [N.Normal]
    (hPC : elementaryAbelianMaxJ (P : Subgroup H) ≤ C)
    (hPN : elementaryAbelianMaxJ (P : Subgroup H) ≤ N) :
    elementaryAbelianMaxJ C ≤ N := by
  obtain ⟨B, hB⟩ := elementaryAbelianMaxSubgroups_nonempty (P : Subgroup H)
  apply sSup_le
  intro A hA
  obtain ⟨S, hAS⟩ := hA.2.1.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S P
  let e := MulAut.conj g
  have hSP : (S : Subgroup H).map e.toMonoidHom = (P : Subgroup H) := by
    change ((g • S : Sylow 2 H) : Subgroup H) = (P : Subgroup H)
    rw [hg]
  have hAP : A.map e.toMonoidHom ≤ (P : Subgroup H) := (map_mono hAS).trans hSP.le
  have hBA : Nat.card B ≤ Nat.card A := hA.2.2 B ((le_sSup hB).trans hPC) hB.2.1
  have hmax : A.map e.toMonoidHom ∈ elementaryAbelianMaxSubgroups (P : Subgroup H) := by
    refine ⟨hAP, hA.2.1.map e.toMonoidHom, ?_⟩
    intro D hDP hD
    rw [card_map_of_injective e.injective]
    exact (hB.2.2 D hDP hD).trans hBA
  have hAN : A.map e.toMonoidHom ≤ N := (le_sSup hmax).trans hPN
  intro a ha
  have hc := (inferInstance : N.Normal).conj_mem (e a)
    (hAN (mem_map_of_mem e.toMonoidHom ha)) g⁻¹
  simpa [e, MulAut.conj_apply, mul_assoc] using hc

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The intrinsic core restricts back to the original `Q_E`. -/
theorem lineQ_subgroupOf (E : Subgroup G) :
    (lineQ E).subgroupOf (lineNormalizer E) = pCore 2 (lineNormalizer E) :=
  comap_map_eq_self_of_injective (lineNormalizer E).subtype_injective _

omit [Finite G] in
/-- The original two-core is in the chosen original Sylow subgroup. -/
theorem lineQ_le_lineT (T E : Subgroup G) (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E) :
    lineQ E ≤ lineT T E := by
  rw [← hU]
  exact map_mono (pCore_isPGroup.le_sylow_of_normal U)

/-- If the Sylow Thompson subgroup were in `Q_E`, all the maximum elementary
subgroups generating the original `I = J(C_G(E))` would be in `Q_E`. -/
theorem lineI_le_lineQ_of_thompson_le (T E : Subgroup G)
    (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hJC : elementaryAbelianMaxJ (lineT T E) ≤ centralizer (E : Set G))
    (hJQ : elementaryAbelianMaxJ (lineT T E) ≤ lineQ E) :
    lineI E ≤ lineQ E := by
  let H := lineNormalizer E
  let C := (centralizer (E : Set G)).subgroupOf H
  let N := (lineQ E).subgroupOf H
  let : N.Normal := by rw [show N = pCore 2 H from lineQ_subgroupOf E]; infer_instance
  have hmap : (elementaryAbelianMaxJ (U : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (lineT T E) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective, hU]
  have hPC : elementaryAbelianMaxJ (U : Subgroup H) ≤ C := by
    intro x hx
    exact hJC (hmap ▸ mem_map_of_mem H.subtype hx)
  have hPN : elementaryAbelianMaxJ (U : Subgroup H) ≤ N := by
    intro x hx
    exact hJQ (hmap ▸ mem_map_of_mem H.subtype hx)
  have hi := map_mono (f := H.subtype) (maxJ_le_normal_of_sylow U C N hPC hPN)
  rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
    show C.map H.subtype = centralizer (E : Set G) from
      map_subgroupOf_eq_of_le (centralizer_le_normalizer (E : Set G)),
    show N.map H.subtype = lineQ E from map_subgroupOf_eq_of_le (map_subtype_le _)] at hi
  exact hi

omit [Finite G] in
/-- The recognized index three forces `I₀`, and hence `I`, outside `M_E`. -/
theorem lineI_not_le_lineM (M T V E : Subgroup G)
    (hindex : (lineI0 T V E ⊓ lineM M E).relIndex (lineI0 T V E) = 3) :
    ¬ lineI E ≤ lineM M E := by
  intro hI
  have hle : lineI0 T V E ≤ lineM M E := inf_le_left.trans hI
  have h := (relIndex_eq_one.mpr (le_inf le_rfl hle))
  rw [hindex] at h
  norm_num at h

/-- Nontriviality of the original Sylow Thompson subgroup modulo the original
core follows from its genuine maximum-elementary family, not an action assumption. -/
theorem sylowThompson_not_le_lineQ (M T V E : Subgroup G)
    (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hTM : T ≤ M)
    (hJC : elementaryAbelianMaxJ (lineT T E) ≤ centralizer (E : Set G))
    (hindex : (lineI0 T V E ⊓ lineM M E).relIndex (lineI0 T V E) = 3) :
    ¬ elementaryAbelianMaxJ (lineT T E) ≤ lineQ E := by
  intro hJQ
  apply lineI_not_le_lineM M T V E hindex
  exact (lineI_le_lineQ_of_thompson_le T E U hU hJC hJQ).trans
    ((lineQ_le_lineT T E U hU).trans (inf_le_inf hTM le_rfl))

/-- In the source notation, `J(R)` has nonidentity image in `G_E/Q_E`. -/
theorem centralizerThompson_not_le_lineQ (M T V E : Subgroup G)
    (hEV : E ≤ V) (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hTM : T ≤ M)
    (hJ : elementaryAbelianMaxJ (lineT T E) =
      elementaryAbelianMaxJ (T ⊓ centralizer (V : Set G)))
    (hindex : (lineI0 T V E ⊓ lineM M E).relIndex (lineI0 T V E) = 3) :
    ¬ elementaryAbelianMaxJ (T ⊓ centralizer (V : Set G)) ≤ lineQ E := by
  rw [← hJ]
  apply sylowThompson_not_le_lineQ M T V E U hU hTM _ hindex
  rw [hJ]
  exact (sSup_le fun _ hA => hA.1).trans (inf_le_right.trans (centralizer_le hEV))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification
