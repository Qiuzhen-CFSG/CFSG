module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Coordinates
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import CFSG.Quasithin.Chapter3.Defs

/-!
# Normality and the value of r in the terminal A₅ argument

Weak closure inside the normal intermediate subgroup O₂(LT) proves normality
in LT; LT need not normalize its Sylow subgroup. The value r = 3 follows
from the order-two intersection in 13.6.24(1) and the escaping centralizer
in 13.6.3(1). These are deductions from earlier source results, not records
containing the parameter or normality conclusions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.6.3, 13.6.24 and the first paragraph of 13.6.25, printed pp.926, 933–934.
The generator-centrality calculation is a separate remaining source step.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters

open Subgroup
open _root_.CFSG.Quasithin.ChapterE

variable {G : Type*} [Group G] [Finite G]

/-- Weak closure in T becomes normal in any overgroup normalizing an
intermediate subgroup R containing it, provided R is still contained in T. -/
theorem weakClosure_normalIn_of_normal_intermediate
    (V T R H : Subgroup G) (i : ℕ)
    (hW : indexedWeakClosure V T i ≤ R) (hRT : R ≤ T)
    (hRH : R ≤ H) (hNR : H ≤ normalizer (R : Set G)) :
    Chapter3.NormalIn (indexedWeakClosure V T i) H := by
  refine ⟨hW.trans hRH, ?_⟩
  intro g hg x hx
  have hRg : R.map (MulAut.conj g).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (hNR hg)
  have hWg := weakClosure_weakly_closed V T i g
    ((map_mono hW).trans (hRg.le.trans hRT))
  have hmem := mem_map_of_mem (MulAut.conj g).toMonoidHom hx
  rw [hWg] at hmem
  exact hmem

/-- Literal normal-core route for 13.6.25(1), using Sylow containment. -/
theorem weakClosure_normalIn_of_le_twoCore
    (V H : Subgroup G) (S : Sylow 2 H) (i : ℕ)
    (hW : indexedWeakClosure V ((S : Subgroup H).map H.subtype) i ≤ H.pCoreIn 2) :
    Chapter3.NormalIn
      (indexedWeakClosure V ((S : Subgroup H).map H.subtype) i) H := by
  apply weakClosure_normalIn_of_normal_intermediate V _ (H.pCoreIn 2) H i hW
    (pCoreIn_le_sylow H S) (pCoreIn_le 2 H)
  simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, H.range_subtype]
    using (pCore 2 H).le_normalizer_map H.subtype

/-- The source centralizer identity also supplies the required containment
in T, without choosing a different Sylow carrier. -/
theorem weakClosure_normalIn_of_centralizer_eq_twoCore
    (V T LT : Subgroup G) (i : ℕ)
    (hcentral : T ⊓ centralizer (V : Set G) = LT.pCoreIn 2)
    (hW : indexedWeakClosure V T i ≤ LT.pCoreIn 2) :
    Chapter3.NormalIn (indexedWeakClosure V T i) LT := by
  apply weakClosure_normalIn_of_normal_intermediate V T (LT.pCoreIn 2) LT i hW
    (by rw [← hcentral]; exact inf_le_left) (pCoreIn_le 2 LT)
  simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, LT.range_subtype]
    using (pCore 2 LT).le_normalizer_map LT.subtype

omit [Finite G] in
private theorem relIndex_mul_card_of_le {U V : Subgroup G} (hUV : U ≤ V) :
    U.relIndex V * Nat.card U = Nat.card V := by
  have hc : Nat.card (U.subgroupOf V) = Nat.card U :=
    Nat.card_congr (subgroupOfEquivOfLe hUV).toEquiv
  simpa only [relIndex, hc] using (U.subgroupOf V).index_mul_card

/-- The small intersection bound alone supplies r ≥ 3 for a group V of
order sixteen. A centralizer element escaping N(V) puts U in V ∩ Vᵍ. -/
theorem three_le_globalR_of_intersections
    (V : Subgroup G) (hcard : Nat.card V = 16)
    (hinter : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2) :
    (3 : ℕ∞) ≤ globalR V := by
  apply le_iInf
  intro U
  apply le_iInf
  rintro ⟨hUV, hnot⟩
  obtain ⟨g, hgU, hgV⟩ := Set.not_subset.mp hnot
  have hUconj : U ≤ V.map (MulAut.conj g).toMonoidHom := by
    intro u hu
    refine ⟨u, hUV hu, ?_⟩
    change g * u * g⁻¹ = u
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hgU u hu).symm
  have hc : Nat.card U ≤ 2 :=
    (Nat.card_le_card_of_injective (Subgroup.inclusion (le_inf hUV hUconj))
      (Subgroup.inclusion_injective _)).trans (hinter g hgV)
  have hm := relIndex_mul_card_of_le hUV
  rw [hcard] at hm
  have hi : 8 ≤ U.relIndex V := by nlinarith
  have hlog : 3 ≤ subgroupCorank V U := by
    exact Nat.le_log_of_pow_le (by decide) hi
  exact_mod_cast hlog

omit [Finite G] in
/-- 13.6.3(1) supplies an actual corank-three witness for the upper bound. -/
theorem globalR_le_three_of_escaping_involution
    (V M : Subgroup G) (z : G) (hzV : z ∈ V) (hz : orderOf z = 2)
    (hcard : Nat.card V = 16) (hNM : normalizer (V : Set G) ≤ M)
    (hescape : ¬ centralizer ({z} : Set G) ≤ M) :
    globalR V ≤ 3 := by
  have hUV : zpowers z ≤ V := zpowers_le.mpr hzV
  have hc : Nat.card (zpowers z) = 2 := by simpa only [Nat.card_zpowers] using hz
  have hm := relIndex_mul_card_of_le hUV
  rw [hc, hcard] at hm
  have hi : (zpowers z).relIndex V = 8 := by omega
  have hnot : ¬ centralizer (zpowers z : Set G) ≤ normalizer (V : Set G) := by
    intro h
    apply hescape
    intro c hc
    apply hNM (h ?_)
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hc
  have h := globalR_le_corank hUV hnot
  norm_num [subgroupCorank, hi, show Nat.log 2 8 = 3 from rfl] at h ⊢
  exact h

/-- The numerical part of 13.6.25(4) from the actual five-point coordinates
and the two preceding source results. -/
theorem globalR_eq_three_from_earlier
    {V : Subgroup G} (d : FiveCoordinates V) (M : Subgroup G)
    (z : G) (hzV : z ∈ V) (hz : orderOf z = 2)
    (hNM : normalizer (V : Set G) ≤ M)
    (hescape : ¬ centralizer ({z} : Set G) ≤ M)
    (hinter : ∀ g : G, g ∉ normalizer (V : Set G) →
      V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) = 2) :
    globalR V = 3 := by
  have hcard : Nat.card V = 16 := by
    calc
      Nat.card V = Nat.card (BinaryPermutation.core (Fin 5)) :=
        Nat.card_congr d.equiv.toEquiv
      _ = 16 := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
          BinaryPermutation.finrank_core]
        rfl
  refine le_antisymm
    (globalR_le_three_of_escaping_involution V M z hzV hz hcard hNM hescape)
    (three_le_globalR_of_intersections V hcard ?_)
  intro g hg
  by_cases h : V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥
  · rw [h]
    simp only [Subgroup.card_bot]
    decide
  · exact (hinter g hg h).le

/-- Literal application of the published 13.6.24 proof: no intersection
bound or r-bound is an extra input. The remaining inputs are 13.2.6,
13.6.2, 13.6.3(1), 13.6.7(1), and the actual A₅ coordinates. -/
theorem globalR_eq_three_from_coordinates
    {V : Subgroup G} [IsElementaryAbelian 2 V]
    (d : FiveCoordinates V) (M : Subgroup G) (v z : V)
    (hv : BinaryPermutation.FiveGeometry.form (d.equiv v).toAdd ≠ 0)
    (hz : z ≠ 1) (hqz : BinaryPermutation.FiveGeometry.form (d.equiv z).toAdd = 0)
    (hAlt : alternatingGroup (Fin 5) ≤ d.actor.range)
    (hfusion : ∀ x : V, x ≠ 1 → ∀ a : G, MulAut.conj a x.val ∈ V →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n x.val = MulAut.conj a x.val)
    [IsMulCommutative (centralizerConjugateClosure V z.val)]
    (hCv : centralizer ({v.val} : Set G) ≤ normalizer (V : Set G))
    (hNM : normalizer (V : Set G) ≤ M)
    (hescape : ¬ centralizer ({z.val} : Set G) ≤ M) :
    globalR V = 3 := by
  apply globalR_eq_three_from_earlier d M z.val z.property
    (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian z.val z.property)
      (fun h => hz (Subtype.ext h))) hNM hescape
  intro g hg hi
  exact (source_13_6_24_from_earlier V d.equiv v z hv hz hqz
    (d.orbits hAlt) hfusion hCv g hg hi).1

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
