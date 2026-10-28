module

public import CFSG.Quasithin.ChapterE.Section06.Obstructions

/-!
# Maximal escaping subspaces and their actual automizer actions

Maximality forces C_V(L) = U for every subgroup L of C_G(U) outside M.
Once a branch constructs V = U[V,X], the actual induced image of X is
nontrivial and supplies the moving element needed by E.6.12. If L is
normal in H and X lies in L, the same generation identity puts C_H(L)
in C_M(V). Normality of an induced image is transported from normalization
of its actual preimage in N_G(V).

These are deductions used in E.6.11, not an assertion of that lemma:
the block/component alternatives must still construct L and X, their
normality, cyclic order, regular action and direct decomposition.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
E.6.11 and its use in E.6.12, printed pp.249–250 (PDF pp.260–261).
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L X : Subgroup G}

omit [Finite G] in
/-- The maximality argument preceding the branch analysis in E.6.11. -/
theorem fixedSpace_eq_of_maximal_escape
    (hUV : U ≤ V)
    (hmax : ∀ W : Subgroup G, U < W → W ≤ V → centralizer (W : Set G) ≤ M)
    (hLH : L ≤ centralizer (U : Set G)) (hLM : ¬ L ≤ M) :
    U = V ⊓ centralizer (L : Set G) := by
  have hUC : U ≤ V ⊓ centralizer (L : Set G) :=
    le_inf hUV (le_centralizer_iff.mpr hLH)
  by_contra he
  have hlt := lt_of_le_of_ne hUC he
  have hC := hmax (V ⊓ centralizer (L : Set G)) hlt inf_le_left
  exact hLM ((le_centralizer_iff.mpr inf_le_right).trans hC)

/-- A constructed decomposition supplies the actual automizer and element required by E.6.12. -/
theorem HypothesisE61.action_escape_of_decomposition
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hn : 1 < subgroupCorank V U)
    (hX : X ≤ M ⊓ centralizer (U : Set G)) (hgen : V = U ⊔ ⁅V, X⁆) :
    inducedAutomizer V X ≠ ⊥ ∧
      ∃ x ∈ M ⊓ centralizer (U : Set G), x ∉ centralizer (V : Set G) := by
  have hXN := hX.trans (h.localCentralizer_le_normalizer hU.2.1 hU.1)
  have hnon : ¬ X ≤ centralizer (V : Set G) := by
    intro hc
    have hcomm : ⁅V, X⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mpr hc)
    have he : V = U := by simpa only [hcomm, sup_bot_eq] using hgen
    subst U
    simp [subgroupCorank] at hn
  refine ⟨fun he => hnon ((inducedAutomizer_eq_bot_iff hXN).mp he), ?_⟩
  obtain ⟨x, hx, hxc⟩ := SetLike.not_le_iff_exists.mp hnon
  exact ⟨x, hX hx, hxc⟩

/-- The deduction of E.6.11(4) from its normal subgroup and decomposition. -/
theorem HypothesisE61.centralizer_le_of_decomposition
    (h : HypothesisE61 K T M V) (hUV : U ≤ V)
    (hLH : L ≤ centralizer (U : Set G))
    (hLn : (L.subgroupOf (centralizer (U : Set G))).Normal)
    (hXL : X ≤ L) (hgen : V = U ⊔ ⁅V, X⁆) :
    centralizer (U : Set G) ⊓ centralizer (L : Set G) ≤
      M ⊓ centralizer (V : Set G) := by
  let _ := h.elementary
  have hVH : V ≤ centralizer (U : Set G) :=
    V.le_centralizer.trans (Subgroup.centralizer_le hUV)
  have hNL := (normal_subgroupOf_iff_le_normalizer hLH).mp hLn
  have hcomm : ⁅V, X⁆ ≤ L := (commutator_mono le_rfl hXL).trans
    (le_normalizer_iff_commutator_le_right.mp (hVH.trans hNL))
  have hc : centralizer (U : Set G) ⊓ centralizer (L : Set G) ≤
      centralizer (V : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hgen]
    apply sup_le
    · exact le_centralizer_iff.mp inf_le_left
    · exact le_centralizer_iff.mp (inf_le_right.trans (Subgroup.centralizer_le hcomm))
  exact le_inf (hc.trans h.centralizer_le) hc

theorem HypothesisE61.normalizer_subspace_le
    (h : HypothesisE61 K T M V) (hU : U ≠ ⊥) (hUV : U ≤ V) :
    M ⊓ normalizer (U : Set G) ≤ normalizer (V : Set G) :=
  inf_normalizer_le_of_trivial_intersections h.ti hU hUV


omit [Finite G] in
/-- Normalization passes to the actual image in Aut(V). -/
theorem inducedAutomizer_normalized {B N : Subgroup G}
    (hBN : B ≤ normalizer (V : Set G)) (hNB : N ≤ normalizer (B : Set G)) :
    inducedAutomizer V N ≤ normalizer (inducedAutomizer V B : Set (Automizer V)) := by
  have hi : N.subgroupOf (normalizer (V : Set G)) ≤
      normalizer (B.subgroupOf (normalizer (V : Set G)) : Set (normalizer (V : Set G))) := by
    rw [← subgroupOf_normalizer_eq hBN]
    exact comap_mono hNB
  exact (map_mono hi).trans (le_normalizer_map V.normalizerMonoidHom.rangeRestrict)

omit [Finite G] in
/-- Relative normality passes to the actual induced automizer subgroup. -/
theorem inducedAutomizer_normal_in {B N : Subgroup G}
    (hBN : B ≤ N) (hNV : N ≤ normalizer (V : Set G))
    (hB : (B.subgroupOf N).Normal) :
    ((inducedAutomizer V B).subgroupOf (inducedAutomizer V N)).Normal := by
  have hle : inducedAutomizer V B ≤ inducedAutomizer V N := map_mono (comap_mono hBN)
  apply (normal_subgroupOf_iff_le_normalizer hle).mpr
  exact inducedAutomizer_normalized (hBN.trans hNV)
    ((normal_subgroupOf_iff_le_normalizer hBN).mp hB)

end CFSG.Quasithin.ChapterE.Section06
