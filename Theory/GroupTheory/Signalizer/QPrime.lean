module
public import Theory.GroupTheory.Signalizer.Subgroup
public import Theory.GroupTheory.Signalizer.Conjugation
public import Theory.GroupAction.InvariantHallContainment
public import Theory.ElementaryAbelian.Basic

/-!
# The common-normalized q-prime subfamily

Let a finite elementary abelian two-group act on a finite group carrying
an odd solvable signalizer family. For a prime q, the new value at a is the
supremum of the subgroups of the original value that are invariant under the
actor, normalized by the original common subgroup, and have order coprime to
q. The constructor has a private body and a public equation for this exact
supremum. The construction assumes no completeness or actor rank bound.

Within each original value, its actor-fixed subgroup is precisely the common
subgroup, by balance. Coprime invariant Hall containment therefore puts every
candidate in any chosen invariant Hall q-prime subgroup of that value. This
bounds the supremum and proves its order remains coprime to q. Invariance and
common normalization pass to the supremum. Intersecting a new value with an
actor's fixed subgroup gives a candidate for the other value, proving balance.

Every original signalizer subgroup of q-coprime order normalized by the
common subgroup is a signalizer subgroup for the new family. New signalizer
subgroups also satisfy the original bounds. The values and generated subgroup
lie in the original ones; the common subgroup normalizes the new generated
subgroup. Value cardinalities decrease strictly wherever q divides an original
value, supplying the numerical input for later induction.

Source: Kurzweil–Stellmacher, *The Theory of Finite Groups*, §11.1.6, printed
p.308, using §8.2.6(d), printed p.187, `refs/latex/kurzweil.tex`. Because all
original values have odd order, their q-prime subgroups automatically exclude
the binary actor prime as required by the source's prime-set formulation.
-/

namespace Theory.GroupTheory.TwoSignalizerFamily

variable {A G : Type*} [Group A] [Group G] [MulDistribMulAction A G]

private def qPrimeValue (θ : TwoSignalizerFamily A G) (q : ℕ)
    (a : {a : A // a ≠ 1}) : Subgroup G :=
  sSup {U : Subgroup G | U ≤ θ.subgroup a ∧ IsInvariant A G U ∧
    θ.common ≤ Subgroup.normalizer (U : Set G) ∧ Nat.Coprime (Nat.card U) q}

private theorem value_le (θ : TwoSignalizerFamily A G) (q : ℕ)
    (a : {a : A // a ≠ 1}) : qPrimeValue θ q a ≤ θ.subgroup a :=
  sSup_le fun _ h => h.1

private theorem value_invariant (θ : TwoSignalizerFamily A G) (q : ℕ)
    (a : {a : A // a ≠ 1}) : IsInvariant A G (qPrimeValue θ q a) := by
  let S := {U : Subgroup G | U ≤ θ.subgroup a ∧ IsInvariant A G U ∧
    θ.common ≤ Subgroup.normalizer (U : Set G) ∧ Nat.Coprime (Nat.card U) q}
  change IsInvariant A G (sSup S)
  rw [sSup_eq_iSup']
  let V : Subgroup G := ⨆ U : S, U.val
  change IsInvariant A G V
  have forward (b : A) (g : G) (hg : g ∈ V) : b • g ∈ V := by
    refine Subgroup.iSup_induction _ (C := fun x => b • x ∈ V) hg ?_ ?_ ?_
    · intro U x hx
      exact (show U.val ≤ V from le_iSup _ U) ((U.property.2.1.invariant b x).mp hx)
    · simp
    · intro x y hx hy
      simpa only [smul_mul'] using Subgroup.mul_mem _ hx hy
  constructor
  intro b g
  exact ⟨forward b g, fun hg => by simpa only [inv_smul_smul] using forward b⁻¹ (b • g) hg⟩

private theorem value_normalized (θ : TwoSignalizerFamily A G) (q : ℕ)
    (a : {a : A // a ≠ 1}) : θ.common ≤ Subgroup.normalizer (qPrimeValue θ q a : Set G) := by
  unfold qPrimeValue
  rw [sSup_eq_iSup']
  exact (le_iInf fun U => U.property.2.2.1).trans
    (Subgroup.iInf_normalizer_le_normalizer_iSup _)

private theorem value_inf_fixed_eq_common (θ : TwoSignalizerFamily A G)
    (a : {a : A // a ≠ 1}) :
    θ.subgroup a ⊓ FixedPoints.subgroup A G = θ.common := by
  apply le_antisymm
  · intro x hx
    apply Subgroup.mem_iInf.mpr
    intro b
    exact θ.balance a b ⟨hx.1, fun c => hx.2 c.val⟩
  · exact le_inf (θ.common_le a) θ.common_le_fixed

private theorem value_coprime [Finite A] [Finite G] [IsElementaryAbelian 2 A]
    (θ : TwoSignalizerFamily A G) (q : ℕ) [Fact q.Prime]
    (a : {a : A // a ≠ 1}) : Nat.Coprime (Nat.card (qPrimeValue θ q a)) q := by
  let K := θ.subgroup a
  let _ : IsInvariant A G K := θ.invariant a
  let π : Set Nat.Primes := {p | p.val ≠ q}
  have hcop : Nat.Coprime (Nat.card A) (Nat.card K) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_left.mpr (θ.odd a)).pow_left n
  obtain ⟨P, hP, hPI⟩ := exists_isHallSubgroup_isInvariant (θ.solvable a) hcop π
  have hbound : qPrimeValue θ q a ≤ P.map K.subtype := by
    apply sSup_le
    intro U hU
    let _ := hU.2.1
    let UH := U.subgroupOf K
    have hUI : IsInvariant A K UH := isInvariant_subgroupOf U K
    have hUcard : Nat.card UH = Nat.card U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU.1).toEquiv
    have hUPi : IsPiSubgroup π UH := by
      intro p hp hpq
      have hdiv : q ∣ Nat.card U := by rwa [hUcard, hpq] at hp
      exact (Fact.out : q.Prime).coprime_iff_not_dvd.mp hU.2.2.2.symm hdiv
    have hUN : FixedPoints.subgroup A K ≤ Subgroup.normalizer (UH : Set K) := by
      intro c hc
      have hcommon : (c : G) ∈ θ.common := by
        rw [← value_inf_fixed_eq_common θ a]
        exact ⟨c.property, fun b => congrArg Subtype.val (hc b)⟩
      rw [← Subgroup.subgroupOf_normalizer_eq hU.1]
      exact hU.2.2.1 hcommon
    have hUP := le_invariant_hall_of_fixed_normalized (θ.solvable a) hcop
      hP hPI hUPi hUI hUN
    intro x hx
    exact ⟨⟨x, hU.1 hx⟩, hUP hx, rfl⟩
  have hPcop : Nat.Coprime (Nat.card P) q := by
    apply Nat.Coprime.symm
    apply (Fact.out : q.Prime).coprime_iff_not_dvd.mpr
    intro hdiv
    exact hP.p_in_pi_of_p_dvd_card ⟨q, Fact.out⟩ hdiv rfl
  have hPmapcop : Nat.Coprime (Nat.card (P.map K.subtype)) q := by
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hPcop
  exact hPmapcop.of_dvd_left (Subgroup.card_dvd_of_le hbound)

open scoped IsMulCommutative

private theorem fixed_invariant [IsMulCommutative A] (B : Subgroup A) :
    IsInvariant A G (FixedPoints.subgroup B G) := by
  have forward (a : A) (x : G) (hx : x ∈ FixedPoints.subgroup B G) :
      a • x ∈ FixedPoints.subgroup B G := by
    intro b
    change b.val • (a • x) = a • x
    calc
      b.val • (a • x) = a • (b.val • x) := by rw [smul_smul, smul_smul, mul_comm]
      _ = a • x := congrArg (fun y : G => a • y) (hx b)
  constructor
  intro a x
  exact ⟨forward a x, fun hx => by simpa only [inv_smul_smul] using forward a⁻¹ (a • x) hx⟩

private theorem common_normalizes_fixed (θ : TwoSignalizerFamily A G) (B : Subgroup A) :
    θ.common ≤ Subgroup.normalizer (FixedPoints.subgroup B G : Set G) :=
  (show θ.common ≤ FixedPoints.subgroup B G from fun _ hx b => θ.common_le_fixed hx b.val).trans
    (FixedPoints.subgroup B G).le_normalizer

variable [Finite A] [Finite G] [IsElementaryAbelian 2 A]

public def qPrime (θ : TwoSignalizerFamily A G) (q : ℕ) [Fact q.Prime] :
    TwoSignalizerFamily A G where
  subgroup a := qPrimeValue θ q a
  odd a := (θ.odd a).of_dvd_nat (Subgroup.card_dvd_of_le (value_le θ q a))
  solvable a := by
    let _ := θ.solvable a
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (value_le θ q a))
  invariant a := value_invariant θ q a
  le_fixed a := (value_le θ q a).trans (θ.le_fixed a)
  balance a b := by
    let _ := value_invariant θ q a
    let _ := fixed_invariant (G := G) (Subgroup.zpowers b.val)
    apply le_sSup
    refine ⟨(inf_le_inf_right _ (value_le θ q a)).trans (θ.balance a b),
      isInvariant_inf _ _, ?_, ?_⟩
    · exact (le_inf (value_normalized θ q a)
        (common_normalizes_fixed θ (Subgroup.zpowers b.val))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    · exact (value_coprime θ q a).of_dvd_left (Subgroup.card_dvd_of_le inf_le_left)

@[simp] public theorem qPrime_subgroup (θ : TwoSignalizerFamily A G) (q : ℕ) [Fact q.Prime]
    (a : {a : A // a ≠ 1}) :
    (θ.qPrime q).subgroup a = sSup {U : Subgroup G | U ≤ θ.subgroup a ∧
      IsInvariant A G U ∧ θ.common ≤ Subgroup.normalizer (U : Set G) ∧
      Nat.Coprime (Nat.card U) q} := by rfl

public theorem qPrime_subgroup_le (θ : TwoSignalizerFamily A G) (q : ℕ) [Fact q.Prime]
    (a : {a : A // a ≠ 1}) : (θ.qPrime q).subgroup a ≤ θ.subgroup a := by
  exact value_le θ q a

public theorem qPrime_coprime (θ : TwoSignalizerFamily A G) (q : ℕ) [Fact q.Prime]
    (a : {a : A // a ≠ 1}) : Nat.Coprime (Nat.card ((θ.qPrime q).subgroup a)) q := by
  exact value_coprime θ q a

public theorem qPrime_normalized_common (θ : TwoSignalizerFamily A G) (q : ℕ) [Fact q.Prime]
    (a : {a : A // a ≠ 1}) :
    θ.common ≤ Subgroup.normalizer ((θ.qPrime q).subgroup a : Set G) := by
  exact value_normalized θ q a

public theorem le_qPrime_subgroup (θ : TwoSignalizerFamily A G) (q : ℕ) [Fact q.Prime]
    (a : {a : A // a ≠ 1}) {U : Subgroup G} (hU : U ≤ θ.subgroup a)
    (hUI : IsInvariant A G U) (hUN : θ.common ≤ Subgroup.normalizer (U : Set G))
    (hUq : Nat.Coprime (Nat.card U) q) : U ≤ (θ.qPrime q).subgroup a := by
  rw [qPrime_subgroup]
  exact le_sSup ⟨hU, hUI, hUN, hUq⟩

public theorem qPrime_card_le (θ : TwoSignalizerFamily A G) (q : ℕ) [Fact q.Prime]
    (a : {a : A // a ≠ 1}) :
    Nat.card ((θ.qPrime q).subgroup a) ≤ Nat.card (θ.subgroup a) :=
  Subgroup.card_le_of_le (θ.qPrime_subgroup_le q a)

public theorem qPrime_card_lt_of_dvd (θ : TwoSignalizerFamily A G) (q : ℕ) [Fact q.Prime]
    (a : {a : A // a ≠ 1}) (hdiv : q ∣ Nat.card (θ.subgroup a)) :
    Nat.card ((θ.qPrime q).subgroup a) < Nat.card (θ.subgroup a) := by
  have hle := θ.qPrime_card_le q a
  have hne : Nat.card ((θ.qPrime q).subgroup a) ≠ Nat.card (θ.subgroup a) := by
    intro heq
    have hcop := θ.qPrime_coprime q a
    rw [heq] at hcop
    exact (Fact.out : q.Prime).coprime_iff_not_dvd.mp hcop.symm hdiv
  omega

public theorem IsSignalizerSubgroup.qPrime {θ : TwoSignalizerFamily A G} {U : Subgroup G}
    (hU : θ.IsSignalizerSubgroup U) (q : ℕ) [Fact q.Prime]
    (hUq : Nat.Coprime (Nat.card U) q)
    (hUN : θ.common ≤ Subgroup.normalizer (U : Set G)) :
    (θ.qPrime q).IsSignalizerSubgroup U := by
  refine ⟨hU.1, hU.2.1, hU.2.2.1, ?_⟩
  intro a
  let _ := hU.2.2.1
  let _ := fixed_invariant (G := G) (Subgroup.zpowers a.val)
  apply θ.le_qPrime_subgroup q a (hU.2.2.2 a) (isInvariant_inf _ _)
  · exact (le_inf hUN (common_normalizes_fixed θ (Subgroup.zpowers a.val))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  · exact hUq.of_dvd_left (Subgroup.card_dvd_of_le inf_le_left)

public theorem IsSignalizerSubgroup.of_qPrime {θ : TwoSignalizerFamily A G}
    (q : ℕ) [Fact q.Prime] {U : Subgroup G} (hU : (θ.qPrime q).IsSignalizerSubgroup U) :
    θ.IsSignalizerSubgroup U := by
  exact ⟨hU.1, hU.2.1, hU.2.2.1, fun a => (hU.2.2.2 a).trans (θ.qPrime_subgroup_le q a)⟩

public theorem qPrime_closure_le (θ : TwoSignalizerFamily A G) (q : ℕ) [Fact q.Prime] :
    (θ.qPrime q).closure ≤ θ.closure := by
  exact iSup_mono fun a => θ.qPrime_subgroup_le q a

public theorem qPrime_closure_normalized_common (θ : TwoSignalizerFamily A G)
    (q : ℕ) [Fact q.Prime] : θ.common ≤ Subgroup.normalizer ((θ.qPrime q).closure : Set G) := by
  exact (le_iInf fun a => θ.qPrime_normalized_common q a).trans
    (Subgroup.iInf_normalizer_le_normalizer_iSup _)

end Theory.GroupTheory.TwoSignalizerFamily
