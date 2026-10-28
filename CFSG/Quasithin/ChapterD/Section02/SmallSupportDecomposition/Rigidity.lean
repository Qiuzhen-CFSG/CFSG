module
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDecomposition.Basic
public import Theory.GroupAction.SmallBinarySupportIrreducible
public import Theory.GroupAction.CommutingIrreducibleSupports
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Rigidity of commuting small-support factors

The supports of the order-three and order-five factors in D.2.12 are
irreducible. Commuting factors consequently either fix each other's
supports or have equal supports. In the equality case their join is
faithful on the common support and acts freely on its nonidentity points.
Distinct factors would give a join of order nine or twenty-five, neither
of which divides three or fifteen.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
D.2.12, printed pp.183–184. No solvability of the ambient group is used.
-/

open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD

variable {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
  [Finite G] [Finite V] [IsElementaryAbelian 2 V]

private theorem factor_irreducible {k : ℕ} (hk : k = 1 ∨ k = 2)
    {X : Subgroup G} (hX : X ∈ smallSupportFactors G V k)
    [IsInvariant X V (commutatorAction X V)]
    (D : Subgroup (commutatorAction X V))
    (hD : IsInvariant X (commutatorAction X V) D) : D = ⊥ ∨ D = ⊤ := by
  let _ := hD
  apply ActionSupport.invariant_eq_bot_or_top_of_small_binary_actor _
    (ActionSupport.fixed_eq_bot_on_coprime_support X (smallSupportFactor_coprime hk hX)) D
  rcases hk with rfl | rfl
  · exact Or.inl ⟨by simpa using hX.2.1, by simpa using hX.2.2⟩
  · exact Or.inr ⟨by simpa using hX.2.1, by simpa using hX.2.2⟩

/-- Commuting small-support factors have equal supports or one fixes the other. -/
public theorem smallSupportFactors_support_eq_or_fixed
    {k : ℕ} (hk : k = 1 ∨ k = 2) {X Y : Subgroup G}
    (hX : X ∈ smallSupportFactors G V k) (hY : Y ∈ smallSupportFactors G V k)
    (hcomm : X ≤ Subgroup.centralizer (Y : Set G)) :
    commutatorAction Y V = commutatorAction X V ∨
      commutatorAction Y V ≤ FixedPoints.subgroup X V := by
  let _ : IsInvariant Y V (commutatorAction Y V) := commutatorAction_isInvariant
  exact ActionSupport.support_eq_or_le_fixed_of_commuting_irreducible Y X hcomm
    (smallSupportFactor_coprime hk hX) (hY.2.2.trans hX.2.2.symm)
    (factor_irreducible hk hY)

/-- Equal nontrivial supports force commuting factors to be equal. -/
public theorem smallSupportFactors_eq_of_commuting_support_eq [FaithfulSMul G V]
    {k : ℕ} (hk : k = 1 ∨ k = 2) {X Y : Subgroup G}
    (hX : X ∈ smallSupportFactors G V k) (hY : Y ∈ smallSupportFactors G V k)
    (hcomm : X ≤ Subgroup.centralizer (Y : Set G))
    (hsupport : commutatorAction Y V = commutatorAction X V) : X = Y := by
  let _ : IsCyclic X := smallSupportFactor_isCyclic hk hX
  let _ : IsMulCommutative X := inferInstance
  have hYX := Subgroup.le_centralizer_iff.mp hcomm
  let H := X ⊔ Y
  let W := commutatorAction X V
  have hHC : H ≤ Subgroup.centralizer (X : Set G) :=
    sup_le (Subgroup.le_centralizer X) hYX
  let _ : IsInvariant H V W := commutatorAction_isInvariant_of_normalizing_actor H X
    (hHC.trans (Subgroup.centralizer_le_normalizer _))
  let _ : IsInvariant X V W := commutatorAction_isInvariant
  let _ : FaithfulSMul H W := ⟨by
    intro a b hab
    apply Subtype.ext
    apply inv_mul_eq_one.mp
    apply ActionSupport.eq_one_of_fixes_support_of_commuting_join X Y hYX
      (smallSupportFactor_coprime hk hX) hsupport.le (a⁻¹ * b)
    intro v hv
    have hh := congrArg Subtype.val (hab (⟨v, hv⟩ : W))
    change (a : G) • v = (b : G) • v at hh
    change ((a : G)⁻¹ * (b : G)) • v = v
    rw [mul_smul, ← hh, inv_smul_smul]⟩
  have hdiv : Nat.card H ∣ Nat.card W - 1 :=
    ActionSupport.card_dvd_card_sub_one_of_commuting_irreducible
      (A := X) (H := H) (W := W) (by
        intro x h w
        apply Subtype.ext
        change (x : G) • ((h : G) • (w : V)) = (h : G) • ((x : G) • (w : V))
        rw [← mul_smul, ← mul_smul,
          (Subgroup.mem_centralizer_iff.mp (hHC h.property)) x x.property])
      (factor_irreducible hk hX)
  by_contra hne
  have hprime : Nat.Prime (2 * k + 1) := by rcases hk with rfl | rfl <;> decide
  have hd : Disjoint X Y := by
    have hcardD : Nat.card (X ⊓ Y : Subgroup G) ∣ 2 * k + 1 := by
      rw [← hX.2.1]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime hprime).mp hcardD with hOne | hFull
    · exact disjoint_iff.mpr (Subgroup.card_eq_one.mp hOne)
    · have heX : X ⊓ Y = X := Subgroup.eq_of_le_of_card_ge inf_le_left (by
        rw [hFull, hX.2.1])
      have hle : X ≤ Y := heX ▸ inf_le_right
      exact (hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hX.2.1, hY.2.1]))).elim
  have hH : Nat.card H = (2 * k + 1) * (2 * k + 1) := by
    rw [Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint X Y
      (hYX.trans (Subgroup.centralizer_le_normalizer _)) hd, hX.2.1, hY.2.1]
  change Nat.card H ∣ Nat.card (commutatorAction X V) - 1 at hdiv
  rw [hH, hX.2.2] at hdiv
  rcases hk with rfl | rfl <;> norm_num at hdiv

/-- Distinct commuting canonical factors fix each other's supports. -/
public theorem smallSupportFactors_cross_fixed_of_commuting [FaithfulSMul G V]
    {k : ℕ} (hk : k = 1 ∨ k = 2) {X Y : Subgroup G}
    (hX : X ∈ smallSupportFactors G V k) (hY : Y ∈ smallSupportFactors G V k)
    (hne : X ≠ Y) (hcomm : X ≤ Subgroup.centralizer (Y : Set G)) :
    commutatorAction Y V ≤ FixedPoints.subgroup X V := by
  rcases smallSupportFactors_support_eq_or_fixed hk hX hY hcomm with heq | hfix
  · exact (hne (smallSupportFactors_eq_of_commuting_support_eq hk hX hY hcomm heq)).elim
  · exact hfix

/-- The symmetric form records both local fixedness conclusions. -/
public theorem smallSupportFactors_mutually_fixed_of_commuting [FaithfulSMul G V]
    {k : ℕ} (hk : k = 1 ∨ k = 2) {X Y : Subgroup G}
    (hX : X ∈ smallSupportFactors G V k) (hY : Y ∈ smallSupportFactors G V k)
    (hne : X ≠ Y) (hcomm : X ≤ Subgroup.centralizer (Y : Set G)) :
    commutatorAction Y V ≤ FixedPoints.subgroup X V ∧
      commutatorAction X V ≤ FixedPoints.subgroup Y V :=
  ⟨smallSupportFactors_cross_fixed_of_commuting hk hX hY hne hcomm,
    smallSupportFactors_cross_fixed_of_commuting hk hY hX hne.symm
      (Subgroup.le_centralizer_iff.mp hcomm)⟩

end CFSG.Quasithin.ChapterD
