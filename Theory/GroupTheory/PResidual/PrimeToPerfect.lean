module

public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Coprime perfectness of the prime-to-p residual

For distinct primes p and q, O^{p′}(G) is q-perfect. Its q-residual
is characteristic in G and still has index prime to p, so the defining
minimality of O^{p′} forces equality. Conversely, a q-perfect group with
a normal q-subgroup and p-group quotient is its own prime-to-p residual.
These facts retain the original subgroup and quotient maps.

Source: the radical I_p=O^{p′}(O∞(L)) in Aschbacher--Smith 3.2.14, p.585.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The prime-to-p residual is q-perfect for every distinct prime q. -/
theorem isPPerfect_primeToResidual (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) : IsPPerfect q (primeToResidual p G) := by
  let R := primeToResidual p G
  let N := (pResidual q R).map R.subtype
  let : N.Characteristic := Subgroup.characteristic_of_characteristic_of_characteristic
  let : N.Normal := inferInstance
  have hcop : Nat.Coprime p N.index := by
    rw [index_map_subtype]
    obtain ⟨n,hn⟩ := (isPGroup_quotient_pResidual (G := R) q).exists_card_eq
    have hN : Nat.Coprime p (pResidual q R).index := by
      rw [index_eq_card,hn]
      exact ((Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : q.Prime)).mpr hpq).pow_right n
    exact hN.mul_right (primeToResidual_index_coprime p)
  have hRN : R ≤ N := primeToResidual_le N hcop
  apply (pResidual_eq_top_iff q R).mp
  apply top_unique
  intro r _
  obtain ⟨s,hs,he⟩ := hRN r.property
  exact R.subtype_injective he ▸ hs

/-- A q-perfect group with normal q-kernel and p-group quotient is generated
by its p-elements. The quotient need not be simple or elementary. -/
theorem primeToResidual_eq_top_of_pGroup_quotient (p q : ℕ) [Fact p.Prime]
    (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup q Q)
    (hquot : IsPGroup p (G ⧸ Q)) (hG : IsPPerfect q G) :
    primeToResidual p G = ⊤ := by
  let R := primeToResidual p G
  let N := R ⊔ Q
  let f : (G ⧸ Q) →* (G ⧸ N) :=
    QuotientGroup.map Q N (MonoidHom.id G) (show Q ≤ N from le_sup_right)
  have hf : Function.Surjective f :=
    QuotientGroup.map_surjective_of_surjective Q N (MonoidHom.id G)
      (QuotientGroup.mk'_surjective _) le_sup_right
  have hN := hquot.of_surjective f hf
  have hc : Nat.Coprime p (Nat.card (G ⧸ N)) := by
    rw [← index_eq_card]
    exact (primeToResidual_index_coprime (G := G) p).coprime_dvd_right
      (index_dvd_of_le (show R ≤ N from le_sup_left))
  have hcard : Nat.card (G ⧸ N) = 1 := hN.card_eq_or_dvd.resolve_right
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hc)
  have hsup : R ⊔ Q = ⊤ := (index_eq_one.mp (by simpa only [index_eq_card] using hcard))
  exact hG R inferInstance (isPGroup_quotient_of_sup_eq_top R Q hQ hsup)

end Subgroup
