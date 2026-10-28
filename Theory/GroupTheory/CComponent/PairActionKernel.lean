module
public import Theory.GroupTheory.CComponent.SimplePairKernel
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.PrimeRankResidualCentralizer

/-!
# Kernels on a two-conjugate simple-core span

A nontrivial ambient homomorphism cannot kill either of two conjugate
C-components whose join is the full orbit. Its normal kernel therefore
intersects their span in a two-group, by the simple-component pair theorem.
Consequently its actual image retains every odd-prime rank of that span.

This is the action-kernel step in the original A₅ specialization of
Aschbacher–Smith C.4.5–8, printed pp.152–154. It makes no faithfulness
assumption and retains the literal homomorphism and its kernel.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G D : Type*} [Group G] [Finite G] [Group D]

/-- The actual restricted kernel on the two-conjugate span is a two-group. -/
theorem pair_span_action_kernel (A : Subgroup G) (hA : A.IsCComponent)
    [IsSimpleGroup (A ⧸ pCore 2 A)]
    (hi : (normalizer (A : Set G)).index = 2)
    (f : G →* D) (hf : (conjugateSpanBy A ⊤).map f ≠ ⊥) :
    IsPGroup 2 (f.comp (conjugateSpanBy A ⊤).subtype).ker := by
  have hn : ¬ (⊤ : Subgroup G) ≤ normalizer (A : Set G) := by
    intro hh
    have he := top_unique hh
    rw [he, index_top] at hi
    omega
  obtain ⟨t, _, ht⟩ := Set.not_subset.mp hn
  let B := A.map (MulAut.conj t).toMonoidHom
  have hm : B ≠ A := fun he => ht (mem_normalizer_iff_map_conj_eq.mpr he)
  let X := conjugateSpanBy A (⊤ : Subgroup G)
  have hpair : A ⊔ B = X := by
    apply le_antisymm
    · refine sup_le (le_conjugateSpanBy A ⊤) ?_
      change B ≤ conjugateSpanBy A ⊤
      rw [conjugateSpanBy_eq_iSup_conj]
      exact le_iSup (fun s : (⊤ : Subgroup G) =>
        A.map (MulAut.conj (s : G)).toMonoidHom) ⟨t, mem_top t⟩
    · change conjugateSpanBy A ⊤ ≤ A ⊔ B
      rw [conjugateSpanBy_eq_iSup_conj]
      apply iSup_le
      intro s
      rcases NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hm (s : G) with he | he
      · exact he.le.trans le_sup_left
      · exact he.le.trans le_sup_right
  have hAX : A ≤ X := le_conjugateSpanBy A ⊤
  have hBX : B ≤ X := hpair ▸ le_sup_right
  have hAf : ¬ A ≤ f.ker := by
    intro hh
    apply hf
    exact bot_unique (map_le_iff_le_comap.mpr
      (conjugateSpanBy_le hh le_normalizer_of_normal))
  have hBf : ¬ B ≤ f.ker := by
    intro hh
    apply hAf
    intro a ha
    have hc := hh (mem_map_of_mem (MulAut.conj t).toMonoidHom ha)
    have hv := (inferInstance : f.ker.Normal).conj_mem _ hc t⁻¹
    simpa [MulAut.conj_apply, mul_assoc] using hv
  let A' := A.subgroupOf X
  let B' := B.subgroupOf X
  let N := (f.comp X.subtype).ker
  have hg : A' ⊔ B' = ⊤ := by
    rw [← subgroupOf_sup hAX hBX, hpair, subgroupOf_self]
  let : (A' ⊔ B').Normal := hg ▸ inferInstance
  let ae := subgroupOfEquivOfLe hAX
  let : IsSimpleGroup (A' ⧸ pCore 2 A') :=
    (QuotientGroup.congr _ _ ae (pCore_map_iso 2 ae)).isSimpleGroup
  let be := (subgroupOfEquivOfLe hBX).trans ((MulAut.conj t).subgroupMap A).symm
  let : IsSimpleGroup (B' ⧸ pCore 2 B') :=
    (QuotientGroup.congr _ _ be (pCore_map_iso 2 be)).isSimpleGroup
  apply isTwoGroup_of_normal_avoiding_simpleCore_pair A' B' ⊥ N
    (hA.subgroupOf hAX) ((hA.map_equiv (MulAut.conj t)).subgroupOf hBX) ?_
    IsPGroup.of_bot (by rw [hg, sup_bot_eq]) ?_ ?_
  · intro he
    apply hm
    have he' := congrArg (map X.subtype) he
    simpa only [A', B', map_subgroupOf_eq_of_le hAX,
      map_subgroupOf_eq_of_le hBX] using he'.symm
  · intro hh
    exact hAf (fun a ha => hh (show (⟨a,hAX ha⟩ : X) ∈ A' from ha))
  · intro hh
    exact hBf (fun b hb => hh (show (⟨b,hBX hb⟩ : X) ∈ B' from hb))

/-- Passing the original span through this action preserves odd-prime ranks. -/
theorem pair_span_action_odd_rank [Finite D]
    (A : Subgroup G) (hA : A.IsCComponent)
    [IsSimpleGroup (A ⧸ pCore 2 A)]
    (hi : (normalizer (A : Set G)).index = 2)
    (f : G →* D) (hf : (conjugateSpanBy A ⊤).map f ≠ ⊥)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p ((conjugateSpanBy A ⊤).map f) = primeRank p (conjugateSpanBy A ⊤) := by
  let X := conjugateSpanBy A (⊤ : Subgroup G)
  have hh := ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel ho
    (f.comp X.subtype) (pair_span_action_kernel A hA hi f hf) ⊤
  rw [← map_map, ← MonoidHom.range_eq_map, range_subtype] at hh
  exact hh.trans (primeRank_equiv p (topEquiv : (⊤ : Subgroup X) ≃* X))

end Theory.GroupTheory
