module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.SubgroupConjugation

/-!
# The two-component orbit in the proof of 13.8.16

An index-two normalizer identifies the T-conjugate span with two actual
conjugates. C-components normalize each other, so their join is the setwise
product. Passing to the generated member of Hz preserves relative component
membership. Finally a Sylow two-subgroup contained in the component normalizer
rules out index two, giving normality inside H.

The normal-or-index-two alternative is the precise earlier output of
Proposition 1.2.1(3). These deductions do not eliminate the nontrivial orbit:
its linear and orthogonal module contradictions remain separate obligations.
The elementary index argument follows the one in
`Chapter1.Section03.Embeddings.Swapped.Factors.Orbit`, without its unrelated
embedding hypotheses.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.16(1), printed pp.952–953 (PDF pp.969–970), and 1.2.1(3), p.504.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped
variable {G : Type*} [Group G]

/-- A nontrivial conjugate span supplies an actual moving element of T. -/
theorem exists_moving_element (K T : Subgroup G)
    (hne : conjugateSpanBy K T ≠ K) :
    ∃ t ∈ T, t ∉ normalizer (K : Set G) := by
  apply Set.not_subset.mp
  intro hn
  exact hne (le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy K T))

/-- Index two makes every T-conjugate one of the two specified subgroups. -/
theorem orbit_eq_two_conjugates (H K T : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H)
    (hi : (normalizer (K.subgroupOf H : Set H)).index = 2)
    {t : G} (ht : t ∈ T) (hm : t ∉ normalizer (K : Set G)) :
    conjugateSpanBy K T = K ⊔ K.conjBy t := by
  let tH : H := ⟨t, hTH ht⟩
  have htH : tH ∉ normalizer (K.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hKH]
    exact hm
  have hconj (s : G) (hs : s ∈ T) : K.conjBy s = K ∨ K.conjBy s = K.conjBy t := by
    by_cases hsn : s ∈ normalizer (K : Set G)
    · exact Or.inl (mem_normalizer_iff_map_conj_eq.mp hsn)
    · have hsH : (⟨s, hTH hs⟩ : H) ∉ normalizer (K.subgroupOf H : Set H) := by
        rw [← subgroupOf_normalizer_eq hKH]
        exact hsn
      have he : tH⁻¹ * (⟨s, hTH hs⟩ : H) ∈ normalizer (K.subgroupOf H : Set H) :=
        (mul_mem_iff_of_index_two hi).mpr (by simp [htH, hsH])
      rw [← subgroupOf_normalizer_eq hKH] at he
      have heq : K.conjBy (t⁻¹ * s) = K := mem_normalizer_iff_map_conj_eq.mp he
      have hh := congrArg (fun B : Subgroup G => B.conjBy t) heq
      rw [conjBy_mul, conjBy_inv'] at hh
      exact Or.inr hh
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨s, hs, k, hk, rfl⟩
    have hmem : s * k * s⁻¹ ∈ K.conjBy s := mem_map_of_mem _ hk
    rcases hconj s hs with he | he
    · exact (le_sup_left : K ≤ K ⊔ K.conjBy t) (he ▸ hmem)
    · exact (le_sup_right : K.conjBy t ≤ K ⊔ K.conjBy t) (he ▸ hmem)
  · refine sup_le (le_conjugateSpanBy K T) ?_
    rintro x ⟨k, hk, rfl⟩
    exact subset_closure ⟨t, ht, k, hk, rfl⟩

/-- Conjugation inside H preserves the actual relative C-component. -/
theorem conjugate_isCComponent (H K : Subgroup G)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {t : G} (ht : t ∈ H) :
    K.conjBy t ≤ H ∧ ((K.conjBy t).subgroupOf H).IsCComponent := by
  have hle : K.conjBy t ≤ H := by
    rintro x ⟨k, hk, rfl⟩
    exact H.mul_mem (H.mul_mem ht (hKH hk)) (H.inv_mem ht)
  refine ⟨hle, ?_⟩
  have hc := hK.map_equiv (MulAut.conj (⟨t, ht⟩ : H))
  have he : (K.subgroupOf H).map (MulAut.conj (⟨t, ht⟩ : H)).toMonoidHom =
      (K.conjBy t).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hle, map_map]
    change (K.subgroupOf H).map ((MulAut.conj t).toMonoidHom.comp H.subtype) = _
    rw [← map_map, map_subgroupOf_eq_of_le hKH]
    rfl
  rwa [he] at hc

/-- The two conjugates generate their setwise product, not merely a larger join. -/
theorem orbit_product [Finite G] (H K T : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hi : (normalizer (K.subgroupOf H : Set H)).index = 2)
    {t : G} (ht : t ∈ T) (hm : t ∉ normalizer (K : Set G)) :
    (conjugateSpanBy K T : Set G) = (K : Set G) * (K.conjBy t : Set G) := by
  rw [orbit_eq_two_conjugates H K T hKH hTH hi ht hm]
  apply coe_mul_of_right_le_normalizer_left
  have hc := (conjugate_isCComponent H K hKH hK (hTH ht)).2
  have hn := (le_cComponentLayer hc).trans (cComponentLayer_le_normalizer hK)
  rw [← subgroupOf_normalizer_eq hKH] at hn
  intro k hk
  exact hn (show (⟨k, (conjugate_isCComponent H K hKH hK (hTH ht)).1 hk⟩ : H) ∈
    (K.conjBy t).subgroupOf H from hk)

/-- After the moving orbit is excluded, Sylow restriction to H rules out index two. -/
theorem normal_of_sylow_span_eq [Finite G] (H K : Subgroup G) (T : Sylow 2 G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (horbit : (K.subgroupOf H).Normal ∨
      (normalizer (K.subgroupOf H : Set H)).index = 2)
    (hspan : conjugateSpanBy K (T : Subgroup G) = K) :
    (K.subgroupOf H).Normal := by
  rcases horbit with hn | hi
  · exact hn
  · have hTN : (T : Subgroup G) ≤ normalizer (K : Set G) := by
      rw [← hspan]
      exact le_normalizer_conjugateSpanBy K (T : Subgroup G)
    have hn : ((T.subtype hTH : Sylow 2 H) : Subgroup H) ≤
        normalizer (K.subgroupOf H : Set H) := by
      rw [Sylow.coe_subtype, ← subgroupOf_normalizer_eq hKH]
      exact subgroupOf_mono H hTN
    have hd := index_dvd_of_le hn
    rw [hi] at hd
    exact ((T.subtype hTH).not_dvd_index hd).elim

/-- Construct the two distinct relative components using the earlier 1.2.1(3) alternative. -/
theorem exists_two_component_orbit [Finite G] (H K T : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (horbit : (K.subgroupOf H).Normal ∨
      (normalizer (K.subgroupOf H : Set H)).index = 2)
    (hne : conjugateSpanBy K T ≠ K) :
    ∃ t ∈ T, t ∉ normalizer (K : Set G) ∧ K.conjBy t ≠ K ∧
      conjugateSpanBy K T = K ⊔ K.conjBy t ∧
      (conjugateSpanBy K T : Set G) = (K : Set G) * (K.conjBy t : Set G) ∧
      K.conjBy t ≤ H ∧ ((K.conjBy t).subgroupOf H).IsCComponent := by
  obtain ⟨t, ht, hm⟩ := exists_moving_element K T hne
  have hi : (normalizer (K.subgroupOf H : Set H)).index = 2 := by
    rcases horbit with hn | hi
    · exact (hne (conjugateSpan_eq_of_normal H K T hKH hTH hn)).elim
    · exact hi
  exact ⟨t, ht, hm, fun he => hm (mem_normalizer_iff_map_conj_eq.mpr he),
    orbit_eq_two_conjugates H K T hKH hTH hi ht hm,
    orbit_product H K T hKH hTH hK hi ht hm,
    conjugate_isCComponent H K hKH hK (hTH ht)⟩

/-- The generated Hz overgroup is inside H and retains the chosen C-component. -/
theorem component_in_generated_overgroup (L₁ T G₁ M H K P : Subgroup G)
    (hH : H ∈ Source.Hz L₁ T G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hKM : ¬ K ≤ M)
    (hP : P ≠ ⊥) (hp : IsPGroup 2 P) (hPbase : P ≤ L₁ ⊔ T)
    (hn : G₁ ≤ normalizer (P : Set G)) :
    let J := conjugateSpanBy K T ⊔ (L₁ ⊔ T)
    J ∈ Source.Hz L₁ T G₁ M ∧ J ≤ H ∧ K ≤ J ∧ (K.subgroupOf J).IsCComponent := by
  dsimp only
  have hKJ : K ≤ conjugateSpanBy K T ⊔ (L₁ ⊔ T) :=
    (le_conjugateSpanBy K T).trans le_sup_left
  have hJH : conjugateSpanBy K T ⊔ (L₁ ⊔ T) ≤ H :=
    sup_le ((conjugateSpanBy_mono le_rfl (le_sup_right.trans hH.1.2)).trans
      (conjugateSpanBy_le_self hKH)) hH.1.2
  exact ⟨generated_overgroup_mem_Hz L₁ T G₁ M H K P hH hKH hKM hP hp hPbase hn,
    hJH, hKJ, hK.subgroupOf_of_le hKJ hJH⟩

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped

end
