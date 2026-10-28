module
public import Mathlib.GroupTheory.Perm.Closure
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.NormNum

/-!
# A transposition normalizer escapes every proper Sylow overgroup in S₅

A Sylow two-subgroup and the centralizer of one of its transpositions generate
S₅. In standard dihedral coordinates a commuting swap combines with a Sylow
word to give a five-cycle, and a five-cycle together with a transposition
generates S₅. Sylow conjugacy transports this to the original marked pair.
The finite certificate checks eight words and five possible connecting swaps;
it does not enumerate subgroups. A representative complete probe used
24 seconds and 1.85 GiB with the default resource limits.

For a surjection onto S₅, the normalizer of the inverse image of a transposition
subgroup consequently escapes every proper subgroup containing the original
Sylow two-subgroup. Kernel containment follows from the putative normalizer
containment, so no separate two-core or elementary-rank hypothesis is needed.

Source application: Aschbacher--Smith, the single alternating case of
2.4.27--29. The quotient marking is supplied by the original local action.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricFive.TranspositionNormalizer
private instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev D := Equiv.Perm (Fin 5)
private def a : D := Equiv.swap 0 1
private def b : D := Equiv.swap 2 3
private def c : D := Equiv.swap 0 2 * Equiv.swap 1 3
private def word : Fin 8 → D := ![1,a,b,a*b,c,a*c,b*c,a*b*c]
private def eight : Subgroup D where
  carrier := Set.range word
  one_mem' := ⟨0,rfl⟩
  mul_mem' := by
    have h : ∀ i j, ∃ k, word i * word j = word k := by decide +kernel
    rintro x y ⟨i,rfl⟩ ⟨j,rfl⟩
    obtain ⟨k,hk⟩ := h i j
    exact ⟨k,hk.symm⟩
  inv_mem' := by
    have h : ∀ i, ∃ j, (word i)⁻¹ = word j := by decide +kernel
    rintro x ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := h i
    exact ⟨j,hj.symm⟩
private theorem eight_card : Nat.card eight = 8 := by
  have hi : Function.Injective word := by decide +kernel
  change Nat.card (Set.range word) = 8
  rw [← Nat.card_congr (Equiv.ofInjective _ hi)]
  simp
private noncomputable def standardSylow : Sylow 2 D := Sylow.ofCard eight (by
  rw [eight_card,Nat.card_eq_fintype_card,Fintype.card_perm]
  norm_num [Nat.factorial]
  decide +kernel)

private theorem connector : ∀ i : Fin 8, (word i).support.card = 2 →
    ∃ j : Fin 5, word i * Equiv.swap j 4 = Equiv.swap j 4 * word i ∧
      (word 5 * Equiv.swap j 4) ^ 5 = 1 ∧ word 5 * Equiv.swap j 4 ≠ 1 := by
  decide +kernel

private theorem standard_generate (τ : D) (ht : τ ∈ eight) (hs : τ.IsSwap)
    (U : Subgroup D) (hP : eight ≤ U) (hC : centralizer ({τ} : Set D) ≤ U) :
    U = ⊤ := by
  obtain ⟨i,rfl⟩ := ht
  obtain ⟨j,hj,hpow,hne⟩ := connector i (Equiv.Perm.card_support_eq_two.mpr hs)
  let σ := word 5 * Equiv.swap j 4
  have ho : orderOf σ = 5 := orderOf_eq_prime_iff.mpr ⟨hpow,hne⟩
  have hσ : σ ∈ U := U.mul_mem (hP ⟨5,rfl⟩)
    (hC (mem_centralizer_singleton_iff.mpr hj.symm))
  have hc : σ.IsCycle := Equiv.Perm.isCycle_of_prime_order'' (by decide) ho
  have hfull : σ.support = Finset.univ := Finset.eq_univ_of_card _ (hc.orderOf ▸ ho)
  have hgen := Equiv.Perm.closure_prime_cycle_swap (by decide : (Fintype.card (Fin 5)).Prime)
    hc hfull hs
  apply top_unique
  rw [← hgen,closure_le,Set.insert_subset_iff,Set.singleton_subset_iff]
  exact ⟨hσ,hP ⟨i,rfl⟩⟩

/-- A Sylow two-subgroup of S₅ and the centralizer of any transposition in it generate S₅. -/
theorem sylow_sup_centralizer_eq_top (P : Sylow 2 (Equiv.Perm (Fin 5)))
    (τ : Equiv.Perm (Fin 5)) (ht : τ ∈ P) (hs : τ.IsSwap) :
    (P : Subgroup _) ⊔ centralizer ({τ} : Set _) = ⊤ := by
  let U := (P : Subgroup D) ⊔ centralizer ({τ} : Set D)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq D P standardSylow
  let e := MulAut.conj g
  have hP : (P : Subgroup D).map e.toMonoidHom = eight := by
    exact congrArg (fun Q : Sylow 2 D => (Q : Subgroup D)) hg
  have ht' : e τ ∈ eight := hP ▸ mem_map_of_mem e.toMonoidHom ht
  have hs' : (e τ).IsSwap := by
    obtain ⟨x,y,hxy,rfl⟩ := hs
    change (g * Equiv.swap x y * g⁻¹).IsSwap
    rw [Equiv.mul_swap_eq_swap_mul,mul_inv_cancel_right]
    exact Equiv.Perm.swap_isSwap_iff.mpr (g.injective.ne hxy)
  have he : U.map e.toMonoidHom = ⊤ := standard_generate (e τ) ht' hs' _
    (hP ▸ map_mono (show (P : Subgroup D) ≤ U from le_sup_left)) (by
      intro x hx
      refine ⟨e.symm x, (le_sup_right : centralizer ({τ} : Set D) ≤ U) ?_, e.apply_symm_apply x⟩
      apply mem_centralizer_singleton_iff.mpr
      apply e.injective
      simpa only [map_mul,e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx)
  have hc := congrArg (Subgroup.comap e.toMonoidHom) he
  rw [comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective U,comap_top] at hc
  exact hc

/-- The inverse image of a transposition subgroup has a normalizer outside
every proper subgroup containing the original Sylow two-subgroup. -/
theorem quotient_normalizer_not_le {H : Type*} [Group H] [Finite H]
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (P : Sylow 2 H) (B A : Subgroup H) (hPB : (P : Subgroup H) ≤ B)
    (hproper : B ≠ ⊤) (τ : Equiv.Perm (Fin 5))
    (ht : τ ∈ P.mapSurjective hq) (hs : τ.IsSwap)
    (hA : A.map q = zpowers τ) :
    ¬ normalizer ((q.ker ⊔ A : Subgroup H) : Set H) ≤ B := by
  intro hN
  let W := q.ker ⊔ A
  have hW : W.map q = zpowers τ := by
    rw [Subgroup.map_sup,Subgroup.map_ker_self,hA,bot_sup_eq]
  have hpre : (zpowers τ).comap q = W := by
    rw [← hW]
    exact comap_map_eq_self le_sup_left
  have hker : q.ker ≤ B :=
    (le_sup_left : q.ker ≤ W).trans (W.le_normalizer.trans hN)
  have hC : centralizer ({τ} : Set _) ≤ B.map q := by
    intro x hx
    obtain ⟨y,rfl⟩ := hq x
    refine mem_map_of_mem q (hN ?_)
    change y ∈ normalizer (W : Set H)
    rw [← hpre]
    apply (le_normalizer_comap (H := zpowers τ) q)
    change q y ∈ normalizer (zpowers τ : Set _)
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    congr 1
    change q y * τ * (q y)⁻¹ = τ
    rw [mem_centralizer_singleton_iff.mp hx,mul_inv_cancel_right]
  have htop : B.map q = ⊤ := by
    apply top_unique
    rw [← sylow_sup_centralizer_eq_top (P.mapSurjective hq) τ ht hs]
    exact sup_le (map_mono hPB) hC
  apply hproper
  have he := congrArg (Subgroup.comap q) htop
  rwa [comap_map_eq_self hker,comap_top] at he

/-- The source form: the marked elementary subgroup lies in the original
Sylow subgroup and its quotient image is generated by a transposition. -/
theorem quotient_normalizer_not_le_of_le_sylow {H : Type*} [Group H] [Finite H]
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (P : Sylow 2 H) (B A : Subgroup H) (hPB : (P : Subgroup H) ≤ B)
    (hproper : B ≠ ⊤) (hAP : A ≤ (P : Subgroup H))
    (τ : Equiv.Perm (Fin 5)) (hs : τ.IsSwap) (hA : A.map q = zpowers τ) :
    ¬ normalizer ((q.ker ⊔ A : Subgroup H) : Set H) ≤ B := by
  apply quotient_normalizer_not_le q hq P B A hPB hproper τ ?_ hs hA
  exact map_mono hAP (hA ▸ mem_zpowers τ)

end Theory.SpecificGroups.SymmetricFive.TranspositionNormalizer
