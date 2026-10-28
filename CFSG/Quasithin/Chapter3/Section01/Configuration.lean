module

public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.ChapterD.Defs
public import Theory.GroupTheory.PResidual.Defs

/-!
# The actual subgroup hypotheses for the QTKE qrc lemma

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Hypothesis
3.1.5 and the first paragraph of the proof of Theorem 3.1.6, p. 573.
The normal elementary abelian subgroup is 2-reduced precisely when its
faithful action image has trivial two-core (Definition B.2.11).

Case (I) normalizes the **residual** `O²(M₀)`, not the core `O₂(M₀)`.
The bridge to D.1.1 proves its unique maximal subgroup and Sylow conditions
from `HStar`. Only the failure of the common-normal branch is additionally
assumed, exactly as in the source proof. No qrc alternative is assumed.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter3

open Subgroup

variable {G : Type*} [Group G]

/-- The concrete local hypotheses 3.1.5. The standing simple QTKE and
maximal two-local assumptions are supplied separately to the theorems
that use them. -/
structure QrcHypotheses (T : Sylow 2 G) (M M₀ H V : Subgroup G) : Prop where
  sylow_le : (T : Subgroup G) ≤ M₀
  left_le : M₀ ≤ M
  right_mem : H ∈ HStar (T : Subgroup G) M
  module_le : V ≤ M₀
  module_normalized : M₀ ≤ normalizer (V : Set G)
  module_elementary : IsElementaryAbelian 2 V
  module_reduced : pCore 2 (ChapterD.internalActionImage M₀ V module_normalized) = ⊥
  core_eq_centralizer : M₀.pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (V : Set G)
  normalizer_cases :
    H ⊓ M ≤ normalizer ((pResidual 2 M₀).map M₀.subtype : Set G) ∨
    H ⊓ M ≤ normalizer (V : Set G)

/-- The genuine common-normal conclusion, without ambient normality in its inputs. -/
def HasCommonNormal (M₀ H R : Subgroup G) : Prop :=
  ∃ N : Subgroup G, N ≤ R ∧ N ≠ ⊥ ∧ NormalIn N (generated M₀ H)

/-- The intrinsic version of 3.1.3(1), for the D.1.1 interface. -/
theorem HStar.unique_maximal_subgroup (T : Sylow 2 G) {M H : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hH : H ∈ HStar (T : Subgroup G) M) :
    ∃! B : Subgroup H, IsCoatom B ∧ (T : Subgroup G) ≤ B.map H.subtype := by
  obtain ⟨hTB, hBH, _⟩ := HStar.unique_maximal T hTM hH
  let B := (H ⊓ M).subgroupOf H
  have hBmap : B.map H.subtype = H ⊓ M := map_subgroupOf_eq_of_le inf_le_left
  have htop : (⊤ : Subgroup H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hBne : B ≠ ⊤ := by
    intro he
    exact hBH.ne (hBmap.symm.trans ((congrArg (map H.subtype) he).trans htop))
  have hBc : IsCoatom B := by
    refine ⟨hBne, ?_⟩
    intro Y hBY
    have hlt : H ⊓ M < Y.map H.subtype := by
      rw [← hBmap]
      exact (map_lt_map_iff_of_injective H.subtype_injective).mpr hBY
    have he := (hBH.eq_or_eq hlt.le (map_subtype_le Y)).resolve_left hlt.ne'
    apply map_injective H.subtype_injective
    exact he.trans htop.symm
  refine ⟨B, ⟨hBc, hBmap.symm ▸ hTB⟩, ?_⟩
  intro Y hY
  have hYH : Y.map H.subtype < H := by
    simpa only [htop] using
      (map_lt_map_iff_of_injective H.subtype_injective).mpr hY.1.lt_top
  have hle : Y ≤ B := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [hBmap]
    exact le_inf hYH.le (HStar.proper_overgroup_le T hH hY.2 hYH)
  by_contra hn
  exact hBne (hY.1.2 B (lt_of_le_of_ne hle hn))

/-- Hypothesis 3.1.5 supplies D.1.1 when its common-normal branch fails. -/
theorem QrcHypotheses.toQRCConfiguration [Finite G]
    {T : Sylow 2 G} {M M₀ H V : Subgroup G}
    (h : QrcHypotheses T M M₀ H V)
    (hn : ¬ HasCommonNormal M₀ H (M₀.pCoreIn 2)) :
    ChapterD.QRCConfiguration M₀ H (T : Subgroup G) V := by
  have hTH : (T : Subgroup G) ≤ H := h.right_mem.1.1.2
  refine ⟨inferInstance, inferInstance,
    ⟨T.subtype h.sylow_le, ?_⟩, ⟨T.subtype hTH, ?_⟩,
    h.module_le, h.module_normalized, h.module_elementary, h.module_reduced,
    HStar.unique_maximal_subgroup T (h.sylow_le.trans h.left_le) h.right_mem,
    h.core_eq_centralizer, ?_⟩
  · exact map_subgroupOf_eq_of_le h.sylow_le
  · exact map_subgroupOf_eq_of_le hTH
  · intro N hN hnorm
    by_contra hne
    apply hn
    refine ⟨N, hN, hne, normalIn_iff_le_normalizer.mpr ⟨?_, ?_⟩⟩
    · exact hN.trans ((pCoreIn_le 2 M₀).trans le_generated_left)
    · rwa [generated_eq_sup]

/-- Uniqueness supplies the failure hypothesis of the qrc bridge. -/
theorem QrcHypotheses.no_common_normal [Finite G]
    {T : Sylow 2 G} {M M₀ H V : Subgroup G}
    (h : QrcHypotheses T M M₀ H V)
    (hu : ∀ L : Subgroup G, IsMaximalTwoLocal L → M₀ ≤ L → L = M) :
    ¬ HasCommonNormal M₀ H (M₀.pCoreIn 2) :=
  no_common_normal_of_unique_maximal (isPGroup_pCoreIn 2 M₀) hu h.right_mem.1.2

end CFSG.Quasithin.Chapter3
