module
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.GeneralizedThompsonTransfer
public import Theory.GroupTheory.PGroup.CyclicInvolution
/-!
# Transfer for the single-block shadows

An involution with no conjugate in a normal subgroup of a Sylow subgroup
has constant nonidentity image when the quotient is cyclic: a finite cyclic
group has a unique involution. Generalized Thompson transfer then detects
that involution outside the ambient commutator. Simplicity and noncommutativity
give the contradiction under the original QTKE hypotheses.

This supplies the transfer implication used in 2.4.22 and on printed p.539.
The application to 2.4.22 retains involution closure and an outside involution
as explicit geometric premises; their construction requires the earlier
single-block lemmas. Source: Aschbacher–Smith, combined manuscript of
1 March 2004, printed pp.537–539.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G]

private theorem involution_not_mem_commutator_of_cyclic_quotient
    (T : Sylow 2 G) (C : Subgroup T) [C.Normal] [IsCyclic (T ⧸ C)]
    (s : T) (hs : orderOf s = 2)
    (hno : ∀ t : T, IsConj (s : G) (t : G) → t ∉ C) :
    (s : G) ∉ _root_.commutator G := by
  let q : T →* T ⧸ C := QuotientGroup.mk' C
  have horder (t : T) (hst : IsConj (s : G) (t : G)) : orderOf (q t) = 2 := by
    have ht : orderOf t = 2 := by
      rw [← orderOf_coe]
      exact (SemiconjBy.orderOf_eq (hst.choose : G) hst.choose_spec).symm.trans ((orderOf_coe s).trans hs)
    apply orderOf_eq_prime
    · rw [← map_pow, show t ^ 2 = 1 by simpa only [ht] using pow_orderOf_eq_one t, map_one]
    · exact fun he => hno t hst ((QuotientGroup.eq_one_iff t).mp he)
  apply Subgroup.not_mem_commutator_of_involution_fusion C s
    (Nat.prime_two.coprime_iff_not_dvd.mpr T.not_dvd_index) hs (hno s (IsConj.refl _))
  intro t hst
  apply (QuotientGroup.eq_one_iff (s⁻¹ * t)).mp
  change q (s⁻¹ * t) = 1
  rw [map_mul, map_inv, IsCyclic.eq_of_orderOf_eq_two (horder t hst) (horder s (IsConj.refl _)),
    inv_mul_cancel]

/-- Under the original simple QTKE hypothesis, every involution class meets the
normal kernel of a cyclic Sylow quotient. -/
theorem cyclic_quotient_forces_involution_fusion {K : GroupClass}
    (hG : IsSimpleQTKE K G) (T : Sylow 2 G)
    (C : Subgroup T) [C.Normal] [IsCyclic (T ⧸ C)]
    (s : T) (hs : orderOf s = 2) :
    ∃ t : T, IsConj (s : G) (t : G) ∧ t ∈ C := by
  let : IsSimpleGroup G := hG.simple
  by_contra hn
  push Not at hn
  have hout := involution_not_mem_commutator_of_cyclic_quotient T C s hs hn
  have htop : _root_.commutator G = ⊤ := by
    rcases (inferInstance : (_root_.commutator G).Normal).eq_bot_or_eq_top with hb | ht
    · exact (hG.nonabelian ((commutator_eq_bot_iff G).mp hb)).elim
    · exact ht
  exact hout (htop ▸ mem_top _)

/-- The transfer step of 2.4.22 from involution closure and an outside involution. -/
theorem quotient_not_cyclic_of_involution_closed {K : GroupClass}
    (hG : IsSimpleQTKE K G) (T : Sylow 2 G)
    (R : Subgroup T) [R.Normal]
    (hclosed : ∀ r t : T, orderOf r = 2 → r ∈ R →
      IsConj (r : G) (t : G) → t ∈ R)
    (s : T) (hs : orderOf s = 2) (hsR : s ∉ R) :
    ¬ IsCyclic (T ⧸ R) := by
  intro hc
  let := hc
  obtain ⟨r, hsr, hr⟩ := cyclic_quotient_forces_involution_fusion hG T R s hs
  have hord : orderOf r = 2 := by
    rw [← orderOf_coe]
    exact (SemiconjBy.orderOf_eq (hsr.choose : G) hsr.choose_spec).symm.trans ((orderOf_coe s).trans hs)
  exact hsR (hclosed r s hord hr hsr.symm)
end CFSG.Quasithin.Chapter2.LinearShadows.Single
