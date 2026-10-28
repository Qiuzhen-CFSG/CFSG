module

public import Theory.Representation.PrimeFixedPointCentralization.Reduction.Actions
public import Theory.GroupAction.CoprimeSmallQuotient
public import Theory.Frattini.CoprimeAction
public import Theory.GroupTheory.PGroup.CoprimeFrattiniAction

/-!
# Group-theoretic consequences of a minimal prime action

A faithful minimal coprime action satisfies `[P,A] = P`. Consequently every
proper invariant normal subgroup is central, in particular the Frattini
subgroup. For a finite q-group this makes the central quotient elementary
abelian. Passing to the Frattini quotient and using its faithful coprime
action proves that a nonidentity prime-order actor fixes only Frattini
elements. Thus the abelian branch is fixed-point-free, while in the
nonabelian branch every such actor fixes exactly the centre.

Source: Aschbacher, *Finite Group Theory*, second edition, Exercise 8.10,
printed p.116 (PDF p.126), used in 36.2 on printed p.194. The exercise's
group-theoretic conclusion is **special**, not **extraspecial**. Its final
extraspecial clause additionally assumes a faithful irreducible representation
of the semidirect product and centralization of the centre. The results here
do not assert that minimality alone makes the centre cyclic or of prime order.
The representation input in `MinimalStructure.lean` supplies cyclicity for
the application; promotion to the extraspecial alternative remains separate.
-/

open Subgroup
open scoped IsMulCommutative

namespace Representation.PrimeFixedPointCentralization

variable {P A : Type*} [Group P] [Group A]

/-- A faithful nontrivial minimal coprime action generates the whole group by
action commutators. Otherwise minimality would kill the second commutator,
and coprime idempotence would make the action trivial. -/
public theorem commutatorAction_eq_top_of_minimal_action
    [Nontrivial A] (φ : A →* MulAut P) (hφ : Function.Injective φ)
    (hmin : IsMinimalAction φ) (hcop : (Nat.card A).Coprime (Nat.card P)) :
    let _ := MulDistribMulAction.compHom P φ
    commutatorAction A P = ⊤ := by
  let _ := MulDistribMulAction.compHom P φ
  by_contra hproper
  have hfix := hmin (commutatorAction A P)
    (fun a z hz => (IsInvariant.invariant
      (self := commutatorAction_isInvariant (G := P) (A := A)) a z).mp hz) hproper
  have hsecond : commutatorAction₂ A P = ⊥ := by
    apply bot_unique
    apply (closure_le _).mpr
    rintro z ⟨a, y, hy, rfl⟩
    change y⁻¹ * φ a y = 1
    rw [hfix a y hy, inv_mul_cancel]
  have hfirst : commutatorAction A P = ⊥ := by
    rw [← commutatorAction₂_eq_commutatorAction_of_coprime hcop, hsecond]
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  apply ha
  apply hφ
  rw [map_one]
  ext z
  have hz : z⁻¹ * φ a z ∈ commutatorAction A P := by
    rw [commutatorAction_eq_closure]
    exact subset_closure ⟨a, z, rfl⟩
  rw [hfirst, mem_bot] at hz
  exact (inv_mul_eq_one.mp hz).symm

/-- Every proper invariant normal subgroup in a faithful minimal coprime
action is central: it is fixed pointwise, hence centralized by all action
commutators, which generate the group. -/
public theorem normal_le_center_of_minimal_action
    [Nontrivial A] (φ : A →* MulAut P) (hφ : Function.Injective φ)
    (hmin : IsMinimalAction φ) (hcop : (Nat.card A).Coprime (Nat.card P))
    (N : Subgroup P) [N.Normal]
    (hN : ∀ a : A, ∀ z ∈ N, φ a z ∈ N) (hproper : N ≠ ⊤) :
    N ≤ center P := by
  let _ := MulDistribMulAction.compHom P φ
  have htop := commutatorAction_eq_top_of_minimal_action φ hφ hmin hcop
  have hcentral := commutatorAction_le_centralizer_of_fixed_normal N
    (hmin N hN hproper)
  rw [htop] at hcentral
  intro z hz
  exact mem_center_iff.mpr fun y => (hcentral (mem_top y) z hz).symm

/-- An abelian group with a faithful nontrivial minimal coprime action has
no nonidentity common fixed point, by the coprime direct-product decomposition. -/
public theorem common_fixed_eq_one_of_minimal_action_of_commutative
    [Finite P] [Finite A] [Nontrivial A] [IsMulCommutative P]
    (φ : A →* MulAut P) (hφ : Function.Injective φ)
    (hmin : IsMinimalAction φ) (hcop : (Nat.card A).Coprime (Nat.card P))
    (z : P) (hz : ∀ a : A, φ a z = z) : z = 1 := by
  let _ := MulDistribMulAction.compHom P φ
  have htop := commutatorAction_eq_top_of_minimal_action φ hφ hmin hcop
  have hsplit := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
    (G := P) (A := A) (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop inferInstance
  exact hsplit.disjoint.le_bot ⟨hz, htop.symm ▸ mem_top z⟩

/-- In the abelian branch, every nonidentity element of a prime-order actor
has trivial fixed subgroup. Such an element generates the actor. -/
public theorem fixed_eq_one_of_minimal_prime_action_of_commutative
    {r : ℕ} [Fact r.Prime] [Finite P] [Finite A] [IsMulCommutative P]
    (hA : Nat.card A = r) (φ : A →* MulAut P) (hφ : Function.Injective φ)
    (hmin : IsMinimalAction φ) (hcop : (Nat.card A).Coprime (Nat.card P))
    (a : A) (ha : a ≠ 1) (z : P) (hz : φ a z = z) : z = 1 := by
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp
    (hA ▸ (Fact.out : r.Prime).one_lt)
  apply common_fixed_eq_one_of_minimal_action_of_commutative φ hφ hmin hcop z
  intro b
  obtain ⟨n, rfl⟩ := mem_powers_of_prime_card hA ha (g' := b)
  induction n with
  | zero => simp
  | succ n ih =>
    change φ (a ^ (n + 1)) z = z
    rw [pow_succ, map_mul]
    change φ (a ^ n) (φ a z) = z
    rw [hz, ih]

/-- The Frattini subgroup is central under a faithful nontrivial minimal
coprime action on a finite group. -/
public theorem frattini_le_center_of_minimal_action
    [Finite P] [Nontrivial A] (φ : A →* MulAut P) (hφ : Function.Injective φ)
    (hmin : IsMinimalAction φ) (hcop : (Nat.card A).Coprime (Nat.card P)) :
    frattini P ≤ center P := by
  apply normal_le_center_of_minimal_action φ hφ hmin hcop (frattini P)
    (fun a z hz => characteristic_iff_le_comap.mp inferInstance (φ a) hz)
  intro htop
  have hbot : (⊥ : Subgroup P) = ⊤ := frattini_nongenerating (by simp [htop])
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  apply ha
  apply hφ
  ext z
  have hz : z = 1 := (mem_bot.mp (hbot.symm ▸ mem_top z))
  simp [hz]

/-- For a finite q-group with a faithful nontrivial minimal coprime action,
the central quotient is elementary abelian. This does not bound the centre. -/
public theorem central_quotient_elementary_of_minimal_action
    {q : ℕ} [Fact q.Prime] [Finite P] [Nontrivial A]
    (hP : IsPGroup q P) (φ : A →* MulAut P) (hφ : Function.Injective φ)
    (hmin : IsMinimalAction φ) (hcop : (Nat.card A).Coprime (Nat.card P)) :
    IsElementaryAbelian q (P ⧸ center P) := by
  let : Fact (IsPGroup q P) := ⟨hP⟩
  have hle := frattini_le_center_of_minimal_action φ hφ hmin hcop
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · exact (Normal.quotient_commutative_iff_commutator_le (N := center P)).mpr
      ((commutator_le_frattini_of_isPGroup (p := q)).trans hle)
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center P) z
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := center P) _).mpr
      (hle (pth_power_mem_frattini_of_isPGroup (p := q) x))

/-- Every fixed element of a nonidentity prime-order actor belongs to the
Frattini subgroup. Apply the abelian branch to the faithful induced action
on the Frattini quotient. -/
public theorem fixed_mem_frattini_of_minimal_prime_action
    {q r : ℕ} [Fact q.Prime] [Fact r.Prime] [Finite P] [Finite A]
    (hP : IsPGroup q P) (hA : Nat.card A = r) (hqr : q ≠ r)
    (φ : A →* MulAut P) (hφ : Function.Injective φ) (hmin : IsMinimalAction φ)
    (a : A) (ha : a ≠ 1) (z : P) (hz : φ a z = z) : z ∈ frattini P := by
  let : Fact (IsPGroup q P) := ⟨hP⟩
  let : IsElementaryAbelian q (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let ψ : A →* MulAut (P ⧸ frattini P) := (quotientAut (frattini P)).comp φ
  have hcop : (Nat.card A).Coprime q := by
    rw [hA]
    exact (Nat.coprime_primes Fact.out Fact.out).mpr hqr.symm
  have hinj : Function.Injective ψ :=
    MonoidHom.injective_frattini_action_of_coprime hP φ hφ hcop
  have hminQ : IsMinimalAction ψ := hmin.of_surjective (QuotientGroup.mk' (frattini P))
    (QuotientGroup.mk'_surjective _) (by intro b x; exact (quotientAut_apply_mk (frattini P) (φ b) x).symm)
  have hcopP : (Nat.card A).Coprime (Nat.card P) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact hcop.pow_right n
  have hcopQ : (Nat.card A).Coprime (Nat.card (P ⧸ frattini P)) :=
    hcopP.of_dvd_right (card_quotient_dvd_card (s := frattini P))
  have hfix : ψ a (QuotientGroup.mk' (frattini P) z) = QuotientGroup.mk' (frattini P) z := by
    change quotientAut (frattini P) (φ a) (QuotientGroup.mk' (frattini P) z) = _
    rw [quotientAut_apply_mk, hz]
  exact (QuotientGroup.eq_one_iff (N := frattini P) z).mp
    (fixed_eq_one_of_minimal_prime_action_of_commutative hA ψ hinj hminQ hcopQ a ha _ hfix)

/-- In the nonabelian branch, each nonidentity prime-order actor fixes
exactly the centre. This conclusion does not require a representation. -/
public theorem fixed_set_eq_center_of_minimal_prime_action
    {q r : ℕ} [Fact q.Prime] [Fact r.Prime] [Finite P] [Finite A]
    (hP : IsPGroup q P) (hA : Nat.card A = r) (hqr : q ≠ r)
    (φ : A →* MulAut P) (hφ : Function.Injective φ) (hmin : IsMinimalAction φ)
    (hproper : center P ≠ ⊤) (a : A) (ha : a ≠ 1) :
    {z | φ a z = z} = (center P : Set P) := by
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp
    (hA ▸ (Fact.out : r.Prime).one_lt)
  have hcop : (Nat.card A).Coprime (Nat.card P) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hA, hn]
    exact ((Nat.coprime_primes Fact.out Fact.out).mpr hqr.symm).pow_right n
  ext z
  constructor
  · intro hz
    exact frattini_le_center_of_minimal_action φ hφ hmin hcop
      (fixed_mem_frattini_of_minimal_prime_action hP hA hqr φ hφ hmin a ha z hz)
  · intro hz
    exact hmin (center P)
      (fun b x hx => characteristic_iff_le_comap.mp inferInstance (φ b) hx)
      hproper a z hz

/-- The complete abelian branch of the structural alternative, using the
original distinct-prime hypotheses. -/
public theorem hasMinimalActionStructure_of_commutative
    {q r : ℕ} [Fact q.Prime] [Fact r.Prime] [Finite P] [Finite A]
    [IsMulCommutative P]
    (hP : IsPGroup q P) (hA : Nat.card A = r) (hqr : q ≠ r)
    (φ : A →* MulAut P) (hφ : Function.Injective φ) (hmin : IsMinimalAction φ) :
    HasMinimalActionStructure q φ := by
  have hcop : (Nat.card A).Coprime (Nat.card P) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hA, hn]
    exact ((Nat.coprime_primes Fact.out Fact.out).mpr hqr.symm).pow_right n
  exact Or.inl ⟨inferInstance,
    fixed_eq_one_of_minimal_prime_action_of_commutative hA φ hφ hmin hcop⟩

end Representation.PrimeFixedPointCentralization
