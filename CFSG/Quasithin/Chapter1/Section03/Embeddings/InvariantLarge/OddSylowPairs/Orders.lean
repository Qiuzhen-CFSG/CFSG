module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddSylowPairs
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.RankOne
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M23.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder


/-!
# Order exclusions for the actual odd-complement Sylow pair

The elementary-square or extraspecial-cube complement forces p² to divide
the carrier order. A bound whose prime-to-six part is squarefree excludes
the small alternating, binary linear, Mathieu and derived rank-two carriers.
These arguments use only the actual pair; no irreducibility of its action
is assumed. Chapter13 applies them to the marked ordinary catalogue.

Source: Aschbacher–Smith, 1.3.4, pp.510–511; 13.1.12(3), p.875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.HasOddSylowPair
open Section02.LocalModels ClassificationModels
variable {A : Type*} [Group A] {p : ℕ} [Fact p.Prime]

private def orderBound : ℕ := 2^10 * 3^3 * 5 * 7 * 11 * 13 * 19 * 23 * 31

private theorem not_square_dvd_orderBound (hp : p.Prime) (hl : 3 < p) :
    ¬ p^2 ∣ orderBound := by
  intro hd
  have hd' : p ∣ orderBound := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hd
  simp only [orderBound, hp.dvd_mul, hp.prime.dvd_pow_iff_dvd (by decide : 10 ≠ 0), hp.prime.dvd_pow_iff_dvd (by decide : 3 ≠ 0),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 19),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 23),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31)] at hd'
  have he : p=5 ∨ p=7 ∨ p=11 ∨ p=13 ∨ p=19 ∨ p=23 ∨ p=31 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [orderBound] at hd

/-- The common order sieve uses no local subgroup classification. -/
theorem not_of_card_dvd_orderBound
    (h : HasOddSylowPair p A) (hp : 3 < p)
    (hc : Nat.card A ∣ 2^10 * 3^3 * 5 * 7 * 11 * 13 * 19 * 23 * 31) : False :=
  not_square_dvd_orderBound (Fact.out : p.Prime) hp (h.prime_square_dvd.trans hc)

/-- None of the alternating Theorem C rows admit the large-prime complement. -/
theorem not_alternating
    (h : HasOddSylowPair p A) (hp : 3 < p)
    (n : ℕ) (hn : 5 ≤ n ∧ n ≤ 8) (he : IsAlternating A n) : False := by
  obtain ⟨e⟩ := he
  apply not_of_card_dvd_orderBound h hp
  rw [Nat.card_congr e.toEquiv]
  obtain ⟨hnlo, hnhi⟩ := hn
  interval_cases n <;> rw [nat_card_alternatingGroup] <;> norm_num

/-- Binary projective degrees three, four and five have no repeated prime above three. -/
theorem not_binary_linear
    (h : HasOddSylowPair p A) (hp : 3 < p)
    (n : ℕ) (hn : n = 3 ∨ n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL A n 2) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  apply not_of_card_dvd_orderBound h hp
  rw [Nat.card_congr e.toEquiv]
  rcases hn with rfl | rfl | rfl
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    rw [hF] at hc
    norm_num [Fin.prod_univ_succ] at hc
    rw [hc]; norm_num
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    rw [hF] at hc
    norm_num [Fin.prod_univ_succ] at hc
    rw [hc]; norm_num
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
    rw [hF] at hc
    norm_num [Fin.prod_univ_succ] at hc
    rw [hc]; norm_num

/-- The five native Mathieu carriers are excluded by their certified orders. -/
theorem not_mathieu
    (h : HasOddSylowPair p A) (hp : 3 < p)
    (name : SporadicName)
    (hname : name = .m11 ∨ name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24)
    (he : Nonempty (A ≃* name.Carrier)) : False := by
  obtain ⟨e⟩ := he
  apply not_of_card_dvd_orderBound h hp
  rw [Nat.card_congr e.toEquiv]
  rcases hname with rfl | rfl | rfl | rfl | rfl
  · change Nat.card Sporadic.Mathieu.M11 ∣ _
    rw [Sporadic.Mathieu.m11_order]; norm_num
  · change Nat.card Sporadic.Mathieu.M12 ∣ _
    rw [Sporadic.Mathieu.m12_order]; norm_num
  · change Nat.card Sporadic.Mathieu.M22 ∣ _
    rw [Sporadic.Mathieu.m22_order]; norm_num
  · change Nat.card Sporadic.Mathieu.M23 ∣ _
    rw [Sporadic.Mathieu.m23_order]; norm_num
  · change Nat.card Sporadic.Mathieu.M24 ∣ _
    rw [Sporadic.Mathieu.m24_order]; norm_num

/-- The field-two symplectic derived row is the actual A₆ carrier. -/
theorem not_symplectic_derived
    (h : HasOddSylowPair p A) (hp : 3 < p)
    (he : Nonempty (A ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) : False := by
  obtain ⟨e⟩ := he
  exact not_alternating h hp 6 (by omega)
    ⟨e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩

/-- The actual binary G₂ derived group has order 6048. -/
theorem not_g2_derived
    (h : HasOddSylowPair p A) (hp : 3 < p)
    (he : Nonempty (A ≃* commutator (Atlas.G2.Model (ZMod 2)))) : False := by
  obtain ⟨e⟩ := he
  apply not_of_card_dvd_orderBound h hp
  rw [Nat.card_congr e.toEquiv, Atlas.G2.DerivedEvenOrder.card_derived_binary (Nat.card_zmod 2)]
  norm_num

/-- The odd linear-three model in the marked catalogue also has squarefree
prime-to-six order. -/
theorem not_linear_three_three (h : HasOddSylowPair p A) (hp : 3 < p)
    (hm : ClassicalGroup.IsPSL A 3 3) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  apply not_of_card_dvd_orderBound h hp
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc
  have hc' : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) = 5616 := by omega
  rw [hc']; norm_num

/-- The exceptional two-cover row PSL₃(4) is excluded already in the quotient. -/
theorem not_linear_three_four (h : HasOddSylowPair p A) (hp : 3 < p)
    (hm : ClassicalGroup.IsPSL A 3 4) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  apply not_of_card_dvd_orderBound h hp
  rw [Nat.card_congr e.toEquiv]
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [hF] at hc
  norm_num [Fin.prod_univ_succ] at hc
  have hc' : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) = 20160 := by omega
  rw [hc']; norm_num

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.HasOddSylowPair
