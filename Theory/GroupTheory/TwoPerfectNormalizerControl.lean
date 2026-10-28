module
public import Theory.GroupTheory.UniqueLocalResidualKernel
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.NormalizerQuotientInner

/-!
# Normalizer control for two-perfect subgroups

In a group with self-centralizing two-core, a nontrivial subgroup normalized
by that core has nontrivial intrinsic two-core. Suppose a Sylow two-subgroup
T normalizes a two-perfect X, and [L,X] lies in O₂(L). Since O₂(L) lies in T,
X is the two-residual of XO₂(L), so L normalizes X. Uniqueness of the maximal
two-local over LT then controls the full normalizer of X. The final lemma
expresses the commutator premise using the literal characteristic quotient
action; its kernel is retained throughout.

Source: Aschbacher–Smith, 14.5.20, assertion (!), printed pp.1018–1019,
refs/quasithin.pdf. ThreeCoreAmbient applies this to the original local lifts.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A nontrivial subgroup normalized by the two-core in a characteristic-two
subgroup has nontrivial intrinsic two-core. -/
theorem pCore_ne_bot_of_core_normalizes
    (J X : Subgroup G) (hXJ : X ≤ J) (hchar : centralizer (pCore 2 J : Set J) ≤ pCore 2 J)
    (hQX : J.pCoreIn 2 ≤ normalizer (X : Set G)) (hne : X ≠ ⊥) :
    pCore 2 X ≠ ⊥ := by
  intro he
  have hi : X ⊓ J.pCoreIn 2 = ⊥ := by
    apply le_bot_iff.mp
    simpa only [pCoreIn, he, map_bot] using inf_pCoreIn_le_of_le 2 hXJ
  have hc : ⁅X,J.pCoreIn 2⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [←hi]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp hQX)
      (le_normalizer_iff_commutator_le_right.mp
        (hXJ.trans (J.le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))))
  have hXQ : X ≤ J.pCoreIn 2 := by
    intro x hx
    have hxc : (⟨x,hXJ hx⟩ : J) ∈ centralizer (pCore 2 J : Set J) := by
      intro q hq
      exact Subtype.ext ((commutator_eq_bot_iff_le_centralizer.mp hc) hx q
        (mem_map_of_mem J.subtype hq))
    exact mem_map_of_mem J.subtype (hchar hxc)
  exact hne (le_bot_iff.mp (hi ▸ le_inf le_rfl hXQ))

/-- Uniqueness over LT controls the full normalizer of a nontrivial
T-invariant two-perfect subgroup centralizing L modulo its two-core. -/
theorem normalizer_le_of_twoPerfect_core_commutator
    (T : Sylow 2 G) (L J M X : Subgroup G)
    (hTJ : (T : Subgroup G) ≤ J) (hchar : centralizer (pCore 2 J : Set J) ≤ pCore 2 J)
    (hXJ : X ≤ J) (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hp : IsPPerfect 2 X) (hne : X ≠ ⊥)
    (hQL : L.pCoreIn 2 ≤ (T : Subgroup G))
    (hc : ⁅L,X⁆ ≤ L.pCoreIn 2)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N=M) :
    normalizer (X : Set G) ≤ M := by
  have hQJ : J.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow J (T.subtype hTJ)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ] at hh
  have hcore := pCore_ne_bot_of_core_normalizes J X hXJ hchar (hQJ.trans hTX) hne
  have hr : (pResidual 2 X).map X.subtype = X := by
    rw [(pResidual_eq_top_iff 2 X).mpr hp,←MonoidHom.range_eq_map,range_subtype]
  have hLX : L ≤ normalizer (X : Set G) := by
    have hh := normalizes_residual_of_commutator_le_two L (T : Subgroup G) X
      (L.pCoreIn 2) hTX hQL (isPGroup_pCoreIn 2 L)
      (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
      (hr.symm ▸ hc)
    rwa [hr] at hh
  obtain ⟨N,hN,hXN⟩ := exists_twoLocal_overgroup_normalizer X (pCore 2 X) hcore pCore_isPGroup
  obtain ⟨R,hNR,hR⟩ := Finite.exists_le_maximal hN
  exact hu R hR ((sup_le hLX hTX).trans (hXN.trans hNR)) ▸ hXN.trans hNR

omit [Finite G] in
/-- The literal quotient-action kernel centralizes modulo the specified characteristic kernel. -/
theorem commutator_le_of_normalizerQuotientAction_eq_one
    (L X : Subgroup G) (N : Subgroup L) [N.Characteristic]
    (hn : X ≤ normalizer (L : Set G))
    (ht : ∀ x : X, normalizerQuotientAction L N (inclusion hn x) = 1) :
    ⁅L,X⁆ ≤ N.map L.subtype := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro x hx l hl
  let a := L.normalizerMonoidHom (inclusion hn (⟨x,hx⟩ : X))
  let l' : L := ⟨l,hl⟩
  have he := congrArg (fun b : MulAut (L ⧸ N) => b (QuotientGroup.mk' N l'))
    (ht ⟨x,hx⟩)
  simp only [normalizerQuotientAction, MonoidHom.comp_apply,
    quotientAut_apply_mk, MulAut.one_apply] at he
  have hz : a l' * l'⁻¹ ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' N (a l' * l'⁻¹) = 1
    rw [map_mul,map_inv]
    rw [show QuotientGroup.mk' N (a l') = QuotientGroup.mk' N l' from he,mul_inv_cancel]
  exact mem_map_of_mem L.subtype hz

end Subgroup
