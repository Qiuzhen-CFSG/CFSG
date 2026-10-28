module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.Quotient
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.OddKernelInvolutionFibers
public import Theory.ElementaryAbelian.Join

/-!
# Product disconnection modulo an odd normal subgroup

Commuting involutions in an odd quotient generate an elementary abelian
two-subgroup. Lift that subgroup isomorphically through a Sylow subgroup
of its preimage. The lifted involutions belong to the distinguished set
because involutions in a fiber are conjugate by the odd kernel. Fusion control
then descends centralizer containment, using the common quotient argument.

Source: GLS, Volume 4, Chapter 2, Lemma 4.5, first paragraph, printed p. 34
(PDF p. 51); compare Chapter 1, Lemma 1.9. This establishes genuine quotient
product disconnection, independently of any recognition conclusion.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Product disconnection descends through an odd normal subgroup in M. -/
public theorem productDisconnected_quotient_of_odd (h : IsProductDisconnected Z M)
    (S : Sylow 2 G) (hSM : (S : Subgroup G) ≤ M)
    (hf : ControlsFusionIn M (S : Subgroup G))
    (N : Subgroup G) [N.Normal] (hNM : N ≤ M) (hodd : Odd (Nat.card N)) :
    IsProductDisconnected ((QuotientGroup.mk' N) '' Z) (M.map (QuotientGroup.mk' N)) := by
  let q := QuotientGroup.mk' N
  have hker : Nat.Coprime 2 (Nat.card q.ker) := by
    simpa only [q, QuotientGroup.ker_mk'] using hodd.coprime_two_left
  apply productDisconnected_quotient_of_product_lifts h S hSM hf N hNM
  intro x hx y hy hinv
  have himg (z : G) (hz : z ∈ Z) : IsInvolution (q z) := by
    refine ⟨?_, by rw [← map_pow, (h.involutions z hz).sq_eq_one, map_one]⟩
    intro he
    exact distinguished_not_mem_normal h N hNM hz ((QuotientGroup.eq_one_iff z).mp he)
  have hxinv := himg x hx
  have hyinv := himg y hy
  have hcomm : Commute (q x) (q y) := by
    have hh : (q x * q y)⁻¹ = q x * q y := by
      simpa only [map_mul] using hinv.inv_eq_self
    rw [mul_inv_rev, hxinv.inv_eq_self, hyinv.inv_eq_self] at hh
    exact hh.symm
  let D : Subgroup (G ⧸ N) := Subgroup.zpowers (q x) ⊔ Subgroup.zpowers (q y)
  let : IsElementaryAbelian 2 D := by
    let := IsElementaryAbelian.zpowers_of_pow_eq_one hxinv.sq_eq_one
    let := IsElementaryAbelian.zpowers_of_pow_eq_one hyinv.sq_eq_one
    apply IsElementaryAbelian.sup_of_le_centralizer
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
    exact (hcomm.zpow_zpow m n).eq
  obtain ⟨P, hP, hmap, _⟩ := Subgroup.exists_elementaryAbelian_map_eq_of_surjective_coprime
    q (QuotientGroup.mk'_surjective N) hker D
  let := hP
  have hxD : q x ∈ D := (show Subgroup.zpowers (q x) ≤ D from le_sup_left) (Subgroup.mem_zpowers _)
  have hyD : q y ∈ D := (show Subgroup.zpowers (q y) ≤ D from le_sup_right) (Subgroup.mem_zpowers _)
  rw [← hmap] at hxD hyD
  obtain ⟨a, haP, hax⟩ := hxD
  obtain ⟨b, hbP, hby⟩ := hyD
  have hainv : IsInvolution a := ⟨fun he => hxinv.ne_one (by rw [← hax, he, map_one]),
    elemPow_eq_one_of_isElementaryAbelian a haP⟩
  have hbinv : IsInvolution b := ⟨fun he => hyinv.ne_one (by rw [← hby, he, map_one]),
    elemPow_eq_one_of_isElementaryAbelian b hbP⟩
  have hmem (z c : G) (hz : z ∈ Z) (hc : IsInvolution c) (he : q z = q c) : c ∈ Z := by
    obtain ⟨g, hg⟩ := Subgroup.involutions_same_image_conj_ker q hker
      (orderOf_eq_prime (h.involutions z hz).sq_eq_one (h.involutions z hz).ne_one)
      (orderOf_eq_prime hc.sq_eq_one hc.ne_one) he
    exact hg ▸ h.invariant (g : G) z hz
  have habimage : q (a * b) = q (x * y) := by rw [map_mul, map_mul, hax, hby]
  refine ⟨a, hmem x a hx hainv hax.symm, b, hmem y b hy hbinv hby.symm,
    ⟨?_, elemPow_eq_one_of_isElementaryAbelian (a * b) (P.mul_mem haP hbP)⟩, habimage⟩
  intro he
  exact hinv.ne_one (by rw [← habimage, he, map_one])

end BenderSuzuki.ZD
