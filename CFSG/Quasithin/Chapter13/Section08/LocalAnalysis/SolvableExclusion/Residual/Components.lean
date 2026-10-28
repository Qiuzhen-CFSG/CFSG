module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Residual.Normalizer
public import Theory.GroupTheory.CComponent.Basic
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Component orbits and the product in 13.8.12(1)

For a genuine C-component whose normalizer has index at most two, its
conjugate span under a Sylow two-subgroup is its full conjugate span in H.
It is consequently normal in H and two-perfect. The product identification
uses normalization of this orbit by H and normalization of L₁ by T.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 1.2.1(3),
printed p.504, and 13.8.12(1), printed p.950. The earlier normal-or-index-two
alternative is explicit; no ordinary quasisimple subgroup substitutes for
the source C-component.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Residual
variable {G : Type*} [Group G] [Finite G]

/-- Sylow two conjugates give the full orbit when its length is at most two. -/
theorem component_span_eq_full (H K : Subgroup G) (T : Sylow 2 G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (horbit : (K.subgroupOf H).Normal ∨
      (normalizer (K.subgroupOf H : Set H)).index = 2) :
    conjugateSpanBy K T = conjugateSpanBy K H := by
  apply le_antisymm (conjugateSpanBy_mono le_rfl hTH)
  rcases horbit with hn | hi
  · have hHK : H ≤ normalizer (K : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hKH).mp hn
    exact (conjugateSpanBy_le le_rfl hHK).trans (le_conjugateSpanBy K T)
  · have hmoving : ¬ (T : Subgroup G) ≤ normalizer (K : Set G) := by
      intro hTN
      have hn : ((T.subtype hTH : Sylow 2 H) : Subgroup H) ≤
          normalizer (K.subgroupOf H : Set H) := by
        rw [Sylow.coe_subtype, ← subgroupOf_normalizer_eq hKH]
        exact subgroupOf_mono H hTN
      have hd := index_dvd_of_le hn
      rw [hi] at hd
      exact (T.subtype hTH).not_dvd_index hd
    obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hmoving
    let tH : H := ⟨t, hTH ht⟩
    have htH : tH ∉ normalizer (K.subgroupOf H : Set H) := by
      rw [← subgroupOf_normalizer_eq hKH]
      exact htn
    apply (closure_le _).mpr
    rintro x ⟨s, hs, k, hk, rfl⟩
    by_cases hsn : s ∈ normalizer (K : Set G)
    · exact le_conjugateSpanBy K T ((mem_normalizer_iff.mp hsn k).mp hk)
    · have hsH : (⟨s, hs⟩ : H) ∉ normalizer (K.subgroupOf H : Set H) := by
        rw [← subgroupOf_normalizer_eq hKH]
        exact hsn
      have he : tH⁻¹ * (⟨s, hs⟩ : H) ∈ normalizer (K.subgroupOf H : Set H) :=
        (mul_mem_iff_of_index_two hi).mpr (by simp [htH, hsH])
      rw [← subgroupOf_normalizer_eq hKH] at he
      have hk' : (t⁻¹ * s) * k * (t⁻¹ * s)⁻¹ ∈ K :=
        (mem_normalizer_iff.mp he k).mp hk
      exact subset_closure ⟨t, ht, _, hk', by group⟩

/-- Two-perfectness is preserved on adjoining conjugates. -/
theorem span_isPPerfect (K T : Subgroup G) (hp : IsPPerfect 2 K) :
    IsPPerfect 2 (conjugateSpanBy K T) := by
  let Y := conjugateSpanBy K T
  have hK : K ≤ twoResidual Y := by
    rw [← twoResidual_eq_self K hp]
    exact twoResidual_mono (le_conjugateSpanBy K T)
  have hn : T ≤ normalizer (twoResidual Y : Set G) :=
    (le_normalizer_conjugateSpanBy K T).trans (normalizer_le_normalizer_twoResidual Y)
  have he : Y = twoResidual Y :=
    le_antisymm (conjugateSpanBy_le hK hn) (twoResidual_le Y)
  change IsPPerfect 2 Y
  rw [he]
  exact isPPerfect_embedded_pResidual 2 _

/-- The actual C-component, including its subnormal carrier, is two-perfect. -/
theorem component_isPPerfect (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) : IsPPerfect 2 K := by
  let := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).surjective
  intro N hN hp
  let := hN
  have hsub : Subsingleton (K ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro k _
  exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)

omit [Finite G] in
/-- This is the product in 13.8.12(1). Normalization concerns the component
orbit and L₁, and does not assume that L₁ normalizes the whole group ⟨K,T⟩. -/
theorem component_overgroup_product (H K L₁ T : Subgroup G)
    (hbase : L₁ ⊔ T ≤ H)
    (horbit : H ≤ normalizer (conjugateSpanBy K T : Set G))
    (hn : T ≤ normalizer (L₁ : Set G)) :
    (((K ⊔ T) ⊔ L₁ : Subgroup G) : Set G) =
      ((K ⊔ T : Subgroup G) : Set G) * (L₁ : Set G) := by
  have he : conjugateSpanBy K T ⊔ T = K ⊔ T := by
    apply le_antisymm
    · exact sup_le (conjugateSpanBy_le le_sup_left
        (le_sup_right.trans (K ⊔ T).le_normalizer)) le_sup_right
    · exact sup_le_sup_right (le_conjugateSpanBy K T) T
  have hj : (K ⊔ T) ⊔ L₁ = conjugateSpanBy K T ⊔ (T ⊔ L₁) := by
    rw [← he, sup_assoc]
  rw [hj, coe_mul_of_right_le_normalizer_left _ _
    ((sup_le (le_sup_right.trans hbase) (le_sup_left.trans hbase)).trans horbit),
    coe_mul_of_left_le_normalizer_right T L₁ hn, ← mul_assoc,
    ← coe_mul_of_right_le_normalizer_left _ _ (le_normalizer_conjugateSpanBy K T), he]

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Residual

end
