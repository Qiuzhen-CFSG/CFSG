module

public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.SolvableQuotientPair
public import Theory.ElementaryAbelian.Quotient
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel

/-!
# Two automorphism quotients from an invariant Frattini flag

Let P be a finite two-group. An Aut(P)-invariant subgroup Q of P/Φ(P)
with |Q| = |(P/Φ(P))/Q| = 16 gives two normal kernels in Aut(P).
Their quotients embed in GL₄(2), whose order is not divisible by 25.
Their intersection is a two-group and hence solvable: its action on the
Frattini quotient squares to one, and Burnside's Frattini automorphism
kernel is a two-group.

Only invariance under automorphisms induced from P is required; Q need
not be characteristic in the elementary abelian Frattini quotient.
The square-one calculation fixes the displacement x⁻¹a(x) in Q.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, Proposition 4.4.10–11, using the two order-sixteen sections of
a Sylow two-subgroup of PSU₅(4).
-/

open Subgroup
open scoped IsMulCommutative

namespace Theory.GroupTheory

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

private theorem not_twentyfive_dvd_aut_sixteen
    (V : Type*) [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) : ¬ 25 ∣ Nat.card (MulAut V) := by
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow V 4 (by simpa using hV)]
  norm_num [Fin.prod_univ_succ]

/-- A preserved flag with two order-sixteen sections supplies two automorphism
quotients with orders avoiding 25 and solvable common kernel. -/
public theorem hasSolvableQuotientPair25_of_invariant_frattini_flag
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (Q : Subgroup (P ⧸ frattini P))
    (hQ : ∀ a : MulAut P, Q.map (quotientAut (frattini P) a).toMonoidHom = Q)
    (hcardQ : Nat.card Q = 16) (hcardquot : Nat.card ((P ⧸ frattini P) ⧸ Q) = 16) :
    HasSolvableQuotientPair 25 (MulAut P) := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.of_injective Q.subtype Q.subtype_injective
  let ρ := quotientAut (frattini P)
  let r := flagRestriction ρ Q hQ
  let q := flagQuotient ρ Q hQ
  have hK : IsPGroup 2 (r.ker ⊓ q.ker : Subgroup (MulAut P)) :=
    flag_kernel_isPGroup ρ (isPGroup_quotientAut_frattini_kernel hP) Q hQ
  let : Group.IsNilpotent (r.ker ⊓ q.ker : Subgroup (MulAut P)) := hK.isNilpotent
  refine ⟨r.ker, q.ker, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro h
    apply not_twentyfive_dvd_aut_sixteen Q hcardQ
    rw [index_ker] at h
    exact h.trans (card_subgroup_dvd_card r.range)
  · intro h
    apply not_twentyfive_dvd_aut_sixteen ((P ⧸ frattini P) ⧸ Q) hcardquot
    rw [index_ker] at h
    exact h.trans (card_subgroup_dvd_card q.range)

end Theory.GroupTheory
