module

public import CFSG.Quasithin.ChapterD.Section02.SmallSupportDecomposition
public import CFSG.Quasithin.ChapterD.Section02.SmallSupportInvolutions
public import Theory.GroupTheory.PrimeSubgroupInvolution
public import Theory.GroupAction.IrreducibleBinaryInvolution

/-!
# The normalized-factor alternative for small-support involutions

Aschbacher--Smith, *The Classification of Quasithin Groups*, D.2.12(3),
`refs/quasithin.pdf`, printed pp.183–184. Normalization of each canonical
factor is an explicit hypothesis; its derivation belongs to the parent module.

On each prime-order factor an involution acts trivially or by inversion.
In the first case irreducibility makes it fix the factor's binary support.
Inversion of one factor saturates the displacement bound, so D.2.11(3)
fixes the complementary fixed space and centralizes all the other factors.
Their odd orders exclude any second inverted factor. Generation gives the
centralizing alternative, including when the canonical family is empty.
-/

open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [Group V] [MulDistribMulAction G V]
  [Finite G] [Finite V] [IsElementaryAbelian 2 V] [FaithfulSMul G V]

omit [FaithfulSMul G V] in
/-- An involution centralizing a canonical factor fixes its support pointwise. -/
public theorem smallSupportFactor_support_fixed_of_centralizes {k : ℕ} (hk : k = 1 ∨ k = 2)
    {X : Subgroup G} (hX : X ∈ smallSupportFactors G V k)
    (t : G) (ht : t ^ 2 = 1) (hc : ∀ x ∈ X, Commute t x) :
    ∀ v ∈ commutatorAction X V, t • v = v := by
  let W := commutatorAction X V
  let _ : IsElementaryAbelian 2 W := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun point =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) (point : V)) }
  let T := Subgroup.zpowers t
  have hnorm : T ≤ Subgroup.normalizer (X : Set G) := by
    apply Subgroup.zpowers_le.mpr
    apply Subgroup.centralizer_le_normalizer
    exact Subgroup.mem_centralizer_iff.mpr (fun x hx => (hc x hx).symm.eq)
  let _ : IsInvariant T V W := commutatorAction_isInvariant_of_normalizing_actor T X hnorm
  let _ : IsInvariant X V W := commutatorAction_isInvariant
  have hfix := fixes_of_sq_eq_one_of_commuting_irreducible_binary (A := X) (W := W)
    (⟨t, Subgroup.mem_zpowers t⟩ : T) (Subtype.ext ht) (by
      intro x w
      apply Subtype.ext
      change (x : G) • (t • (w : V)) = t • ((x : G) • (w : V))
      simp only [← mul_smul, (hc x x.property).eq]) (by
      intro D hD
      let _ := hD
      apply ActionSupport.invariant_eq_bot_or_top_of_small_binary_actor _
        (ActionSupport.fixed_eq_bot_on_coprime_support X (smallSupportFactor_coprime hk hX)) D
      rcases hk with rfl | rfl
      · exact Or.inl ⟨by simpa using hX.2.1, by simpa using hX.2.2⟩
      · exact Or.inr ⟨by simpa using hX.2.1, by simpa using hX.2.2⟩)
  intro v hv
  exact congrArg Subtype.val (hfix ⟨v, hv⟩)

omit [Finite G] [Finite V] [IsElementaryAbelian 2 V] [FaithfulSMul G V] in
private theorem not_inverted {k : ℕ} (hk : k = 1 ∨ k = 2)
    {X : Subgroup G} (hX : X ∈ smallSupportFactors G V k)
    (t : G) (hc : ∀ x ∈ X, Commute t x) :
    ¬ (∀ x ∈ X, t * x * t⁻¹ = x⁻¹) := by
  intro hi
  have hbot : X = ⊥ := by
    apply bot_unique
    intro x hx
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (show Nat.Coprime 2 (2 * k + 1) by
      rcases hk with rfl | rfl <;> decide)
    · apply orderOf_dvd_of_pow_eq_one
      have he : x = x⁻¹ := by simpa only [(hc x hx).eq, mul_inv_cancel_right] using hi x hx
      rw [pow_two]
      exact inv_eq_iff_mul_eq_one.mp he.symm
    · simpa only [hX.2.1] using Subgroup.orderOf_dvd_natCard X hx
  have hh := (Subgroup.card_eq_one.mpr hbot).symm.trans hX.2.1
  rcases hk with rfl | rfl <;> norm_num at hh


/-- Inversion of one canonical factor uses the entire involution displacement.
Every other factor and its support are consequently centralized. -/
public theorem smallSupportFactor_inverted_full_support {k : ℕ} (hk : k = 1 ∨ k = 2)
    {X : Subgroup G} (hX : X ∈ smallSupportFactors G V k)
    (t : G) (ht : IsInvolution t)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers t) V) = 2 ^ k)
    (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹) :
    commutatorAction (Subgroup.zpowers t) V =
      commutatorSubgroup (Subgroup.zpowers t) V (commutatorAction X V) ∧
    ∀ Y ∈ smallSupportFactors G V k, Y ≠ X →
      (∀ y ∈ Y, Commute t y) ∧ (∀ v ∈ commutatorAction Y V, t • v = v) := by
  have hodd : Odd (Nat.card X) := by
    rw [hX.2.1]
    rcases hk with rfl | rfl <;> decide
  have hsquare : Nat.card (commutatorAction X V) =
      Nat.card (commutatorAction (Subgroup.zpowers t) V) ^ 2 := by
    rw [hX.2.2, hcard, ← pow_mul, Nat.mul_comm k 2]
  have hfaith : fixingSubgroup G (Set.univ : Set V) = ⊥ := by
    apply bot_unique
    intro g hg
    apply eq_of_smul_eq_smul (α := V)
    intro v
    simpa only [one_smul] using ((mem_fixingSubgroup_iff (M := G)).mp hg v (Set.mem_univ v))
  obtain ⟨heq, hfix, hcentral⟩ :=
    invertedOddSubgroup_full_support X hodd t ht hinv hsquare hfaith
  refine ⟨heq, ?_⟩
  intro Y hY hne
  constructor
  · intro y hy
    apply Commute.symm
    apply hcentral y
    · intro x hx
      exact (show Commute x y from
        Subgroup.mem_centralizer_iff.mp
          (smallSupportFactors_commutingFamily hk Y hY X hX hy) x hx).symm
    · intro v hv
      exact smallSupportFactors_cross_fixed hk hY hX hne hv ⟨y, hy⟩
  · intro v hv
    exact hfix v (smallSupportFactors_cross_fixed hk hX hY hne.symm hv)

/-- D.2.12(3), assuming explicitly that the involution normalizes each factor.
Either every factor and support is centralized, including their generated
subgroup and its support, or exactly one factor is inverted. The first branch
also covers an empty canonical family. -/
public theorem smallSupportFactors_normalized_involution_alternative {k : ℕ} (hk : k = 1 ∨ k = 2)
    (t : G) (ht : IsInvolution t)
    (hcard : Nat.card (commutatorAction (Subgroup.zpowers t) V) = 2 ^ k)
    (hnorm : ∀ X ∈ smallSupportFactors G V k,
      t ∈ Subgroup.normalizer (X : Set G)) :
    ((∀ X ∈ smallSupportFactors G V k,
      (∀ x ∈ X, Commute t x) ∧ (∀ v ∈ commutatorAction X V, t • v = v)) ∧
      (∀ x ∈ smallSupportGroup G V k, Commute t x) ∧
      (∀ v ∈ commutatorAction (smallSupportGroup G V k) V, t • v = v)) ∨
    ∃ X ∈ smallSupportFactors G V k,
      (∀ x ∈ X, t * x * t⁻¹ = x⁻¹) ∧
      (∀ Y ∈ smallSupportFactors G V k,
        (∀ y ∈ Y, t * y * t⁻¹ = y⁻¹) → Y = X) ∧
      commutatorAction (Subgroup.zpowers t) V =
        commutatorSubgroup (Subgroup.zpowers t) V (commutatorAction X V) ∧
      ∀ Y ∈ smallSupportFactors G V k, Y ≠ X →
        (∀ y ∈ Y, Commute t y) ∧ (∀ v ∈ commutatorAction Y V, t • v = v) := by
  classical
  by_cases hc : ∀ X ∈ smallSupportFactors G V k, ∀ x ∈ X, Commute t x
  · left
    have hfix (X) (hX : X ∈ smallSupportFactors G V k) :=
      smallSupportFactor_support_fixed_of_centralizes hk hX t ht.2 (hc X hX)
    refine ⟨fun X hX => ⟨hc X hX, hfix X hX⟩, ?_, ?_⟩
    · have hle : smallSupportGroup G V k ≤ Subgroup.centralizer {t} := by
        rw [smallSupportGroup_eq_iSup]
        apply iSup_le
        intro X x hx
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hc X.val X.property x hx).symm.eq
      intro x hx
      exact (show Commute x t from Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm
    · have hle : commutatorAction (smallSupportGroup G V k) V ≤
          FixedPoints.subgroup (Subgroup.zpowers t) V := by
        rw [smallSupportGroup_support_eq_iSup]
        apply iSup_le
        intro X v hv a
        exact smul_eq_self_of_mem_zpowers a.property (hfix X.val X.property v hv)
      intro v hv
      exact hle hv ⟨t, Subgroup.mem_zpowers t⟩
  · push Not at hc
    obtain ⟨X, hX, x, hx, htx⟩ := hc
    have hp : (Nat.card X).Prime := by
      rw [hX.2.1]
      rcases hk with rfl | rfl <;> decide
    have hinv := (centralizes_or_inverts_prime_subgroup_of_sq_eq_one X hp t ht.2 (hnorm X hX)).resolve_left
      (fun hc => htx (hc x hx))
    obtain ⟨heq, hother⟩ := smallSupportFactor_inverted_full_support hk hX t ht hcard hinv
    right
    refine ⟨X, hX, hinv, ?_, heq, hother⟩
    intro Y hY hiY
    by_contra hne
    exact not_inverted hk hY t (hother Y hY hne).1 hiY

end CFSG.Quasithin.ChapterD
