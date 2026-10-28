module
public import Theory.GroupTheory.PGroup.OmegaCoprimeAction
public import Mathlib.GroupTheory.Transfer
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.PResidual.NormalComplement

/-!
# Normal complements detected by a central section

A cyclic Sylow p-subgroup has a unique subgroup of order p. If a normal
subgroup A contains p-elements and [A,G] lies in a subgroup of order prime
to p, that subgroup of order p is fixed by its Sylow normalizer. The
omega-restriction kernel is a p-group, while the Sylow normalizer action
has order prime to p. Burnside transfer therefore gives a normal
p-complement.

Source application: Aschbacher–Smith 14.7.21(1), printed p.1049, with
G = C_K R₁, A = L₁ and Q = O₂(L₁). Normality is required only for A;
this criterion does not require C_K R₁ to be normal in a larger group.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Fixing the prime roots of an abelian Sylow forces its whole normalizer to centralize it. -/
theorem normalizer_le_centralizer_of_fixed_prime_roots
    (S : Sylow p G) [IsMulCommutative S]
    (hfix : ∀ n ∈ normalizer (S : Set G), ∀ x ∈ (S : Subgroup G),
      x^p=1 → n*x=x*n) :
    normalizer (S : Set G) ≤ centralizer (S : Set G) := by
  let a := (S : Subgroup G).normalizerMonoidHom
  have hle : a.range ≤ (OmegaAction.omegaRestriction S p 1).ker := by
    rintro b ⟨n,rfl⟩
    change n ∈ ((OmegaAction.omegaRestriction S p 1).comp a).ker
    apply (OmegaAction.mem_ker_restriction_iff a p 1 n).mpr
    intro x hx
    apply Subtype.ext
    change (n : G) * (x : G) * (n : G)⁻¹ = x
    have hp : (x : G)^p=1 := by
      simpa only [pow_one,Subgroup.coe_pow,Subgroup.coe_one] using congrArg Subtype.val hx
    rw [hfix n n.property x x.property hp,mul_assoc,mul_inv_cancel,mul_one]
  have hr : IsPGroup p a.range :=
    (OmegaAction.restriction_kernel_isPGroup S.isPGroup').to_le hle
  obtain ⟨k,hk⟩ := hr.exists_card_eq
  have hc : (centralizer (S : Set G)).relIndex (normalizer (S : Set G)) = p^k := by
    rw [←index_ker,normalizerMonoidHom_ker] at hk
    exact hk
  have hi : (centralizer (S : Set G)).relIndex (normalizer (S : Set G)) ∣
      (S : Subgroup G).index :=
    (relIndex_dvd_of_le_left _ S.le_centralizer).trans
      (relIndex_dvd_index_of_le S.le_normalizer)
  have hcop : Nat.Coprime ((S : Subgroup G).index) (p^k) :=
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr S.not_dvd_index).symm.pow_right k
  exact relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop hi (hc ▸ dvd_rfl))

/-- Burnside transfer when the Sylow normalizer fixes every prime root. -/
theorem hasNormalPComplement_of_fixed_prime_roots
    (S : Sylow p G) [IsMulCommutative S]
    (hfix : ∀ n ∈ normalizer (S : Set G), ∀ x ∈ (S : Subgroup G),
      x^p=1 → n*x=x*n) : HasNormalPComplement p G := by
  have hc := S.normalizer_le_centralizer_of_fixed_prime_roots hfix
  let f := MonoidHom.transferSylow S hc
  refine ⟨f.ker, inferInstance, ?_, ?_⟩
  · exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (MonoidHom.not_dvd_card_ker_transferSylow S hc)
  · exact S.isPGroup'.of_equiv
      (MonoidHom.ker_transferSylow_isComplement' S hc).symm.QuotientMulEquiv.symm

/-- A central section of a normal subgroup detects the prime roots of a cyclic Sylow. -/
theorem hasNormalPComplement_of_cyclic_of_central_section
    (S : Sylow p G) [IsCyclic S] (A Q : Subgroup G) [A.Normal]
    (hpA : p ∣ Nat.card A) (hpQ : Nat.Coprime p (Nat.card Q))
    (hcomm : ⁅A, (⊤ : Subgroup G)⁆ ≤ Q) : HasNormalPComplement p G := by
  obtain ⟨U,hU⟩ := S.exists_subgroupOf_eq_of_normal A
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' p (U.dvd_card_of_dvd_card hpA)
  have haS : (a : A).val ∈ (S : Subgroup G) := by
    change (a : A) ∈ (S : Subgroup G).subgroupOf A
    rw [←hU]
    exact a.property
  let b : S := ⟨(a : A).val,haS⟩
  have hb : orderOf b = p := calc
    orderOf b = orderOf (b : G) := (orderOf_injective
      (S : Subgroup G).subtype (S : Subgroup G).subtype_injective b).symm
    _ = orderOf (a : A) := orderOf_injective A.subtype A.subtype_injective (a : A)
    _ = orderOf a := orderOf_injective (U : Subgroup A).subtype
      (U : Subgroup A).subtype_injective a
    _ = p := ha
  let W := omega S (p := p) 1
  have hWcard : Nat.card W ≤ p := by
    rw [show W = (powMonoidHom (p^1) : S →* S).ker from OmegaAction.omega_eq_pow_ker p 1,
      IsCyclic.card_powMonoidHom_ker, pow_one]
    exact Nat.gcd_le_right _ (Fact.out : p.Prime).pos
  have hBW : zpowers b ≤ W := by
    apply zpowers_le.mpr
    apply subset_closure
    change b ^ (p^1) = 1
    simpa only [pow_one,←hb] using pow_orderOf_eq_one b
  have hBW' : zpowers b = W := eq_of_le_of_card_ge hBW (by
    rw [Nat.card_zpowers,hb]
    exact hWcard)
  have hWA : W ≤ A.subgroupOf (S : Subgroup G) := by
    rw [←hBW']
    exact zpowers_le.mpr (a : A).property
  have hdis : Disjoint (S : Subgroup G) Q := by
    obtain ⟨k,hk⟩ := S.isPGroup'.exists_card_eq
    exact disjoint_of_coprime_natCard (hk ▸ hpQ.pow_left k)
  apply S.hasNormalPComplement_of_fixed_prime_roots
  intro n hn x hx hxp
  have hxA : x ∈ A := hWA (subset_closure (show (⟨x,hx⟩ : S)^(p^1)=1 by
    apply Subtype.ext
    change x^(p^1)=1
    simpa only [pow_one] using hxp))
  have hq : ⁅x,n⁆ ∈ Q := hcomm (commutator_mem_commutator hxA (mem_top n))
  have hs : ⁅x,n⁆ ∈ (S : Subgroup G) := by
    simpa only [commutatorElement_def,mul_assoc] using
      S.mul_mem hx (((mem_normalizer_iff.mp hn) x⁻¹).mp (S.inv_mem hx))
  exact (commutatorElement_eq_one_iff_mul_comm.mp (disjoint_def.mp hdis hs hq)).symm
end Sylow
