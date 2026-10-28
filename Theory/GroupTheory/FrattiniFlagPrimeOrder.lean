module
public import Theory.GroupTheory.FrattiniFlagQuotientPair

/-!
# Prime divisors detected by a preserved Frattini flag

An automorphism preserving a flag in an elementary two-group and acting
trivially on both sections has square one. For a two-group P the common
kernel of the two induced actions is therefore a two-group, using the
Burnside basis kernel. If both sections have order sixteen, primes absent
from |GL₄(2)| are absent from Aut(P). The exterior Hall application uses 31
and the actual Sylow flag of PSU₅(4).
Source: Aschbacher--Smith 4.4.10--11, printed p.621.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.FrattiniFlagPrimeOrder

private def flagRestriction {A V : Type*} [Group A] [Group V]
    (ρ : A →* MulAut V) (Q : Subgroup V)
    (hQ : ∀ a : A, Q.map (ρ a).toMonoidHom = Q) : A →* MulAut Q where
  toFun a := ((ρ a).subgroupMap Q).trans (MulEquiv.subgroupCongr (hQ a))
  map_one' := by ext x; change ρ 1 x = x; rw [map_one]; rfl
  map_mul' a b := by ext x; change ρ (a * b) x = ρ a (ρ b x); rw [map_mul]; rfl

private def flagQuotient {A V : Type*} [Group A] [Group V]
    (ρ : A →* MulAut V) (Q : Subgroup V) [Q.Normal]
    (hQ : ∀ a : A, Q.map (ρ a).toMonoidHom = Q) : A →* MulAut (V ⧸ Q) where
  toFun a := QuotientGroup.congr Q Q (ρ a) (hQ a)
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q x
    change QuotientGroup.mk' Q (ρ 1 x) = QuotientGroup.mk' Q x
    rw [map_one]; rfl
  map_mul' a b := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q x
    change QuotientGroup.mk' Q (ρ (a * b) x) =
      QuotientGroup.mk' Q (ρ a (ρ b x))
    rw [map_mul]; rfl

private theorem flag_kernel_square {A V : Type*} [Group A] [Group V]
    [IsElementaryAbelian 2 V] (ρ : A →* MulAut V) (Q : Subgroup V)
    (hQ : ∀ a : A, Q.map (ρ a).toMonoidHom = Q)
    (a : ((flagRestriction ρ Q hQ).ker ⊓ (flagQuotient ρ Q hQ).ker : Subgroup A)) :
    ρ a.val ^ 2 = 1 := by
  have hinv (x : V) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) x
  have hfix (x : Q) : ρ a.val x = x :=
    congrArg (fun f : MulAut Q => (f x : V)) a.property.1
  ext x
  have he := MulEquiv.congr_fun (MonoidHom.mem_ker.mp a.property.2)
    (QuotientGroup.mk' Q x)
  have hdelta : x⁻¹ * ρ a.val x ∈ Q := QuotientGroup.eq.mp he.symm
  have hh := hfix ⟨_, hdelta⟩
  change ρ a.val (x⁻¹ * ρ a.val x) = x⁻¹ * ρ a.val x at hh
  simp only [map_mul, hinv] at hh
  change ρ a.val (ρ a.val x) = x
  apply mul_left_cancel (a := ρ a.val x)
  exact hh.trans (mul_comm _ _)

private theorem flag_kernel_isPGroup {A V : Type*} [Group A] [Group V]
    [IsElementaryAbelian 2 V] (ρ : A →* MulAut V) (hρ : IsPGroup 2 ρ.ker)
    (Q : Subgroup V) (hQ : ∀ a : A, Q.map (ρ a).toMonoidHom = Q) :
    IsPGroup 2 ((flagRestriction ρ Q hQ).ker ⊓ (flagQuotient ρ Q hQ).ker : Subgroup A) := by
  intro a
  have hsquare : a.val ^ 2 ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact flag_kernel_square ρ Q hQ a
  obtain ⟨n, hn⟩ := hρ ⟨a.val ^ 2, hsquare⟩
  refine ⟨n + 1, ?_⟩
  apply Subtype.ext
  have hn' : (a.val ^ 2) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  change a.val ^ (2 ^ (n + 1)) = 1
  rw [pow_succ, Nat.mul_comm, pow_mul]
  exact hn'


private theorem card_aut_sixteen {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 16) : Nat.card (MulAut E) = 20160 := by
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E 4 (by simpa using hE)]
  norm_num [Fin.prod_univ_succ]

/-- Every prime absent from GL₄(2) is absent from the automorphism group
of a two-group with two invariant order-sixteen Frattini sections. -/
theorem not_dvd_aut_of_invariant_flag
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (Q : Subgroup (P ⧸ frattini P))
    (hQ : ∀ a : MulAut P, Q.map (quotientAut (frattini P) a).toMonoidHom = Q)
    (hcardQ : Nat.card Q = 16) (hcardquot : Nat.card ((P ⧸ frattini P) ⧸ Q) = 16)
    {p : ℕ} (hp : p.Prime) (hpfree : ¬ p ∣ 20160) :
    ¬ p ∣ Nat.card (MulAut P) := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.of_injective Q.subtype Q.subtype_injective
  let ρ := quotientAut (frattini P)
  let r := flagRestriction ρ Q hQ
  let q := flagQuotient ρ Q hQ
  let f := r.prod q
  have hK : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_prod]
    exact flag_kernel_isPGroup ρ (isPGroup_quotientAut_frattini_kernel hP) Q hQ
  have hcount : Nat.card f.ker * Nat.card f.range = Nat.card (MulAut P) := by
    rw [← index_ker]
    exact f.ker.card_mul_index
  intro hd
  rw [← hcount] at hd
  rcases hp.dvd_mul.mp hd with hk | hr
  · obtain ⟨n,hn⟩ := hK.exists_card_eq
    rw [hn] at hk
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow hk)
    exact hpfree (by subst p; decide)
  · have hd' := hr.trans f.range.card_subgroup_dvd_card
    rw [Nat.card_prod,card_aut_sixteen hcardQ,card_aut_sixteen hcardquot] at hd'
    exact (hp.not_dvd_mul hpfree hpfree) hd'

end Theory.GroupTheory.FrattiniFlagPrimeOrder
