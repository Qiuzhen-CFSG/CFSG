module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.SylowThompson
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Stellmacher.BaumannNormalizer

/-!
# Characteristic-normalizer control from the earlier ordering maximality

Frattini in `C_M(V)` shows that `N_M(C_T(V))` covers the action of `M` on
its source module. The ordering maximality in 15.3.2(5) then makes this a
uniqueness subgroup. Since it normalizes `Baum(C_T(V))`, it controls the
normalizers of every nontrivial characteristic subgroup of that Baumann
subgroup. This proves the control implication on p.1153 without assuming
it or confusing `C(G,B)` with an ordinary centralizer.

The remaining maximum-elementary-family calculation must identify the
Baumann subgroup of `T_E` with this one before applying the result to `B_E`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.2(5),
A.5.7, and the first paragraph of the proof of 15.3.67, printed p.1153.
-/

public section
open Subgroup Stellmacher
open CFSG.Quasithin.ChapterA.Section05To06
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
variable {G : Type*} [Group G] [Finite G]

private theorem orderingLE_normalizer_lineR (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) :
    OrderingLE T M (M ⊓ normalizer (lineR T (localModule T M) : Set G)) := by
  let V := localModule T M
  let C := (centralizer (V : Set G)).subgroupOf M
  have hMV : M ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy _ _
  let _ : C.Normal := normal_subgroupOf_of_le_normalizer
    (hMV.trans (normalizer_le_normalizer_centralizer _))
  obtain ⟨P, hP⟩ := (T.subtype hTM).exists_subgroupOf_eq_of_normal C
  let R := (P : Subgroup C).map C.subtype
  have hR : R.map M.subtype = lineR T V := by
    rw [show R = (P : Subgroup C).map C.subtype from rfl, hP, map_map]
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨hc, c.property⟩
    · intro hx
      exact ⟨⟨⟨x, hTM hx.1⟩, hx.2⟩, hx.1, rfl⟩
  have hfr : normalizer (R : Set M) ⊔ C = ⊤ := P.normalizer_sup_eq_top
  intro m hm
  have hm' : (⟨m, hm⟩ : M) ∈ normalizer (R : Set M) ⊔ C := hfr ▸ mem_top _
  obtain ⟨n, hn, c, hc, he⟩ := mem_sup_of_normal_right.mp hm'
  have hnR : (n : G) ∈ normalizer (R.map M.subtype : Set G) :=
    R.le_normalizer_map M.subtype (mem_map_of_mem M.subtype hn)
  rw [hR] at hnR
  exact ⟨n, ⟨n.property, n.property, hnR⟩, c, ⟨c.property, hc⟩, congrArg Subtype.val he⟩

/-- Frattini and 15.3.2(5) make `N_M(C_T(V))` a uniqueness subgroup. -/
theorem lineR_normalizer_unique (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsOrderingMaximal T M) :
    ∀ N : Subgroup G, IsMaximalTwoLocal N →
      M ⊓ normalizer (lineR T (localModule T M) : Set G) ≤ N → N = M := by
  have hMV : M ≤ normalizer (localModule T M : Set G) := le_normalizer_conjugateSpanBy _ _
  have hTR : (T : Subgroup G) ≤ normalizer (lineR T (localModule T M) : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      (hM.1.2.trans (hMV.trans (normalizer_le_normalizer_centralizer _)))).trans
        inf_normalizer_le_normalizer_inf
  intro N hN hle
  exact (lemma_A_5_7_1 hM (le_inf hM.1.2 hTR) inf_le_left
    (orderingLE_normalizer_lineR T M hM.1.2) N hN).mp hle

/-- The whole characteristic-normalizer closure of `Baum(C_T(V))` lies in `M`. -/
theorem lineR_baumann_control (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsOrderingMaximal T M) :
    (ChapterB.baumann (lineR T (localModule T M))).characteristicNormalizerClosure ≤ M := by
  exact characteristicNormalizerClosure_le_of_unique_maximalTwoLocal
    (lineR_normalizer_unique T M hM)
    (T.isPGroup'.to_le (show ChapterB.baumann (lineR T (localModule T M)) ≤
      (T : Subgroup G) from inf_le_left.trans inf_le_left))
    (inf_le_right.trans (normalizer_le_normalizer_baumann _))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
