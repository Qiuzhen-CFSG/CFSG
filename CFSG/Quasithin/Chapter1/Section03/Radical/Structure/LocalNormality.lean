module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.QuotientShape

/-!
# Local normality and maximal radical normalizers

The proof of A.3.8(3), printed p.46, explicitly shows that a nonnormal
C-component of a two-core-free SQTK group is quasisimple. We use this exact
universal implication, still as an earlier-source parameter, on the quotient
of LT. The C-component quotient correspondence lifts normality back to LT;
characteristic transport then gives T-invariance of Ξ_p(L).

For maximal L, 1.2.7(3) concerns the normalizer of the T-conjugate closure
of L. Invariance identifies that closure with L. To compare N_G(L) with
N_G(Ξ_p(L)), we place the latter inside the normalizer of its nontrivial
two-core, which is a two-local subgroup. Maximal two-locality now applies.
The two-core is nontrivial using the exact earlier 1.1.3(1)/1.1.4(6) inputs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.8(3),
pp.45–46, and the proofs of 1.3.3 and 1.3.8, pp.509 and 512.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02
namespace CFSG.Quasithin.Chapter1
universe u
variable {G : Type u} [Group G]

/-- The normal-or-quasisimple implication proved in A.3.8(3) lifts through O₂. -/
theorem radicalLocal_invariant_of_A38 [Finite G] {𝒦 : GroupClass.{u}}
    (hA38 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    {T L₀ : Subgroup G} (hL : L₀ ∈ L G T)
    (hQ : IsSQTK 𝒦 ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) :
    T ≤ normalizer (L₀ : Set G) := by
  let := pCore_isNilpotent (p := 2) (G := (L₀ ⊔ T : Subgroup G))
  rcases hA38 _ hQ (pCore_quotient_pCore_eq_bot 2) _ (hL.1.map_quotient _) with hN | hC
  · have hh := cComponent_normal_of_quotient_normal hL.1 _ hN
    exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
      (show L₀ ≤ L₀ ⊔ T from le_sup_left)).mp hh)
  · let := hC
    exact (hn (IsQuasisimple.of_mulEquiv (radicalLocalQuotientEquiv hL).symm)).elim

/-- Every radical subgroup inherits T-invariance from its defining component. -/
theorem XiRad_invariant_of_A38 [Finite G] {𝒦 : GroupClass.{u}}
    (hA38 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    {T : Subgroup G}
    (hQ : ∀ L₀ ∈ L G T,
      IsSQTK 𝒦 ((L₀ ⊔ T : Subgroup G) ⧸ pCore 2 (L₀ ⊔ T : Subgroup G)))
    {X : Subgroup G} (hX : X ∈ XiRad G T) : T ≤ normalizer (X : Set G) := by
  obtain ⟨L₀, hL, hn, p, _, _, _, rfl⟩ := hX
  exact XiP_invariant p (radicalLocal_invariant_of_A38 hA38 hL (hQ L₀ hL) hn)

/-- When T normalizes L, its conjugate closure is exactly L. -/
theorem radical_componentOrbit_eq {L₀ T : Subgroup G}
    (hT : T ≤ normalizer (L₀ : Set G)) : componentOrbit L₀ T = L₀ := by
  apply le_antisymm _ (le_componentOrbit L₀ T)
  apply iSup_le
  intro t
  exact (mem_normalizer_iff_map_conj_eq.mp (hT t.property)).le

/-- The maximality and uniqueness clauses of 1.2.7(3) for an invariant component. -/
theorem radical_normalizer_maximal_of_127 {T L₀ : Subgroup G}
    (h127 : ∀ K ∈ LStar G T,
      IsMaximalTwoLocal (normalizer (componentOrbit K T : Set G)) ∧
        ∀ M : Subgroup G, IsMaximalTwoLocal M → K ⊔ T ≤ M →
          M = normalizer (componentOrbit K T : Set G))
    (hL : L₀ ∈ LStar G T) (hT : T ≤ normalizer (L₀ : Set G)) :
    IsMaximalTwoLocal (normalizer (L₀ : Set G)) ∧
      ∀ M : Subgroup G, IsMaximalTwoLocal M → L₀ ⊔ T ≤ M →
        M = normalizer (L₀ : Set G) := by
  simpa only [radical_componentOrbit_eq hT] using h127 L₀ hL

/-- Either prescribed odd quotient shape forces Ξ_p(L) to be nontrivial. -/
theorem XiP_ne_bot_of_oddQuotient {p : ℕ} (hp : p.Prime) (L₀ : Subgroup G)
    (hq : XiOddQuotient p (XiQuotient (XiP p L₀))) : XiP p L₀ ≠ ⊥ := by
  intro he
  have : Subsingleton (XiP p L₀) := by rw [he]; infer_instance
  have : Subsingleton (XiQuotient (XiP p L₀)) := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (XiP p L₀)) a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (XiP p L₀)) b
    exact congrArg (QuotientGroup.mk' (pCore 2 (XiP p L₀))) (Subsingleton.elim x y)⟩
  have hc : Nat.card (XiQuotient (XiP p L₀)) = 1 := Nat.card_eq_one_iff_unique.mpr
    ⟨inferInstance, inferInstance⟩
  have := hq.one_lt_card hp
  omega

/-- Local characteristic two forces a nontrivial intrinsic two-core. -/
theorem XiP_pCoreIn_ne_bot {p : ℕ} (hp : p.Prime) {T L₀ : Subgroup G}
    (hL : L₀ ∈ L G T) (hT : T ≤ normalizer (L₀ : Set G))
    (hq : XiOddQuotient p (XiQuotient (XiP p L₀)))
    (h113 : ∀ M ∈ He G, ∀ N : Subgroup G, N ≠ ⊥ → N ≤ M →
      (N.subgroupOf M).IsSubnormal → N ∈ He G)
    (h114 : HOver G (T : Set G) ⊆ He G) : (XiP p L₀).pCoreIn 2 ≠ ⊥ := by
  have hn := XiP_ne_bot_of_oddQuotient hp L₀ hq
  have hHe : XiP p L₀ ∈ He G := by
    have hjoin := h114 ⟨XiP_join_mem_H p hL,
      show T ≤ XiP p L₀ ⊔ T from le_sup_right⟩
    have hnorm : ((XiP p L₀).subgroupOf (XiP p L₀ ⊔ T)).Normal :=
      normal_subgroupOf_of_le_normalizer
        (sup_le (XiP p L₀).le_normalizer (XiP_invariant p hT))
    exact h113 _ hjoin _ hn le_sup_left hnorm.isSubnormal
  intro he
  apply hn
  change XiP p L₀ ⊓ centralizer ((XiP p L₀).pCoreIn 2 : Set G) ≤
    (XiP p L₀).pCoreIn 2 at hHe
  apply bot_unique
  intro x hx
  apply he ▸ hHe
  refine ⟨hx, ?_⟩
  intro y hy
  have hy1 : y = 1 := hy
  simp [hy1]
/-- Maximality among two-local subgroups suffices for the normalizer equality. -/
theorem XiP_normalizer_eq_of_maximalTwoLocal (p : ℕ) (L₀ : Subgroup G)
    (hM : IsMaximalTwoLocal (normalizer (L₀ : Set G)))
    (hcore : (XiP p L₀).pCoreIn 2 ≠ ⊥) :
    normalizer (L₀ : Set G) = normalizer (XiP p L₀ : Set G) := by
  have hNX := normalizer_le_normalizer_XiP p L₀
  have hNC : normalizer (XiP p L₀ : Set G) ≤
      normalizer ((XiP p L₀).pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image (XiP p L₀) (pCore 2 (XiP p L₀))
  have hlocal : IsTwoLocal (normalizer ((XiP p L₀).pCoreIn 2 : Set G)) :=
    ⟨(XiP p L₀).pCoreIn 2, hcore, isPGroup_pCoreIn 2 (XiP p L₀), rfl⟩
  exact le_antisymm hNX (hNC.trans (hM.2 hlocal (hNX.trans hNC)))

end CFSG.Quasithin.Chapter1
