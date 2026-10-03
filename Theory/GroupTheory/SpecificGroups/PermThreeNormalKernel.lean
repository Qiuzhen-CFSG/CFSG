module
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum

/-!
# A normal kernel containing a two-subgroup outside an S3 kernel

Let a finite group map onto the symmetric group on three letters, with a
two-group kernel Q. If a normal subgroup K contains a two-subgroup D not
contained in Q, then the quotient by K is a two-group. No maximality property
of Q is needed: an actual two-core is one application of the statement.

The nontrivial image of D has order two. The normal image of K therefore
has even order dividing six. Order two would make it central in S3, whose
center is trivial, so the image is all of S3. Every coset modulo K then has
a representative in Q, and the quotient is a homomorphic image of Q.
In particular, the two-residual lies in K by residual minimality.

This source-neutral implication supplies the normal action-kernel step in
Stellmacher (10.1), Journal of Algebra 190 (1997). Its consumer supplies the
actual action and identifies the kernel of the local SL₂(2) quotient.
-/

namespace Subgroup

private theorem normal_perm_three_eq_top_of_contains_two
    (K D : Subgroup (Equiv.Perm (Fin 3))) [K.Normal]
    (hD : IsPGroup 2 D) (hDK : D ≤ K) (hne : D ≠ ⊥) : K = ⊤ := by
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hd := D.card_subgroup_dvd_card
  rw [hcard] at hd
  have hcop : Nat.Coprime (Nat.card D) 3 := by
    obtain ⟨n, hn⟩ := hD.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hd2 : Nat.card D ∣ 2 := hcop.dvd_mul_right.mp hd
  have hDcard : Nat.card D = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with hc | hc
    · exact (hne (Subgroup.card_eq_one.mp hc)).elim
    · exact hc
  have hKdvd : Nat.card K ∣ 6 := hcard ▸ K.card_subgroup_dvd_card
  have htwo : 2 ∣ Nat.card K := hDcard ▸ Subgroup.card_dvd_of_le hDK
  have hKsmall : Nat.card K ≤ 6 := Nat.le_of_dvd (by decide) hKdvd
  have hKnot : Nat.card K ≠ 2 := by
    intro heq
    have hcentral := central_of_normal_card_two K heq
    have hsmall : ∀ x : Equiv.Perm (Fin 3), (∀ y, y*x=x*y) → x=1 := by decide +kernel
    have hbot : K = ⊥ := by
      apply le_antisymm ?_ bot_le
      intro x hx
      exact hsmall x (mem_center_iff.mp (hcentral hx))
    have hc := card_eq_one.mpr hbot
    omega
  have hKcard : Nat.card K = 6 := by
    interval_cases hn : Nat.card K <;> norm_num at *
  apply eq_top_of_card_eq
  rwa [hcard]

/-- A normal subgroup containing an escaping two-subgroup has two-group
quotient when the specified two-kernel quotient is S3. -/
public theorem quotient_isPGroup_two_of_perm_three_normal_kernel
    {G : Type*} [Group G] [Finite G]
    (Q K D : Subgroup G) [K.Normal] (hQ : IsPGroup 2 Q)
    (f : G →* Equiv.Perm (Fin 3)) (hsurj : Function.Surjective f)
    (hker : f.ker = Q) (hD : IsPGroup 2 D) (hDK : D ≤ K) (hDnot : ¬ D ≤ Q) :
    IsPGroup 2 (G ⧸ K) := by
  let _ : (K.map f).Normal := (inferInstance : K.Normal).map f hsurj
  have hDne : D.map f ≠ ⊥ := by
    intro heq
    exact hDnot (hker ▸ (map_eq_bot_iff D).mp heq)
  have himage : K.map f = ⊤ :=
    normal_perm_three_eq_top_of_contains_two (K.map f) (D.map f)
      (hD.map f) (map_mono hDK) hDne
  let π : G →* G ⧸ K := QuotientGroup.mk' K
  apply hQ.of_surjective (π.comp Q.subtype)
  intro point
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K point
  obtain ⟨k, hk, heq⟩ := (show f g ∈ K.map f by rw [himage]; trivial)
  have hq : g * k⁻¹ ∈ Q := by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, heq, mul_inv_cancel]
  refine ⟨⟨g * k⁻¹, hq⟩, ?_⟩
  change π (g * k⁻¹) = π g
  rw [map_mul, map_inv, show π k = 1 from (QuotientGroup.eq_one_iff _).mpr hk]
  simp

end Subgroup
