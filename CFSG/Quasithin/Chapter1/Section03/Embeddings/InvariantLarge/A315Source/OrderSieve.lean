module
public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Source
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.SourceTransport.Action
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.RankOne
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M23.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.SpecificGroups.Janko1.Model
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder


/-!
# Order exclusions for the large-prime intrinsic complement

The original complement is elementary of order p² or extraspecial of order
p³, so containment forces p² to divide the component order. A single integer
with squarefree prime-to-six part bounds all relevant alternating, binary
linear, Mathieu and J₁ orders. Their concrete cardinality theorems exclude
every p > 3. The actual binary symplectic and G₂ derived models are included.
The independent rank-one cyclicity theorem also closes every Bender row.

The source small rank-two dispatch is thereby reduced to genuine triality(2)
and Tits; neither remaining finite case is asserted here.
Source: Aschbacher–Smith A.3.15, pp.50–51, and 1.3.4, pp.510–511.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source
open Section02.LocalModels ClassificationModels
variable {J : Type*} [Group J] {D B : Subgroup J} {S : Sylow 2 J} {p : ℕ}

/-- The intrinsic complement forces a repeated prime in the component order. -/
theorem prime_square_dvd_component (hB : XiOddQuotient p B) (hBD : B ≤ D) :
    p^2 ∣ Nat.card D := by
  apply dvd_trans _ (card_dvd_of_le hBD)
  rcases hB with ⟨_, hc⟩ | ⟨_, hc, _⟩
  · rw [hc]
  · rw [hc]
    exact pow_dvd_pow p (by decide : 2 ≤ 3)

private def orderBound : ℕ := 2^10 * 3^3 * 5 * 7 * 11 * 19 * 23 * 31

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
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 19),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 23),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31)] at hd'
  have he : p=5 ∨ p=7 ∨ p=11 ∨ p=19 ∨ p=23 ∨ p=31 := by omega
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [orderBound] at hd

/-- The common order sieve uses no local subgroup classification. -/
theorem not_of_card_dvd_orderBound
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (hc : Nat.card D ∣ 2^10 * 3^3 * 5 * 7 * 11 * 19 * 23 * 31) : False :=
  not_square_dvd_orderBound hA.prime hA.large
    ((prime_square_dvd_component hB.oddComplement hA.inside).trans hc)

/-- None of the alternating Theorem C rows admit the large-prime complement. -/
theorem not_alternating
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (n : ℕ) (hn : 5 ≤ n ∧ n ≤ 8) (he : IsAlternating D n) : False := by
  obtain ⟨e⟩ := he
  apply not_of_card_dvd_orderBound hA hB
  rw [Nat.card_congr e.toEquiv]
  obtain ⟨hnlo, hnhi⟩ := hn
  interval_cases n <;> rw [nat_card_alternatingGroup] <;> norm_num

/-- Binary projective degrees three, four and five have no repeated prime above three. -/
theorem not_binary_linear
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (n : ℕ) (hn : n = 3 ∨ n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL D n 2) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  apply not_of_card_dvd_orderBound hA hB
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
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (name : SporadicName)
    (hname : name = .m11 ∨ name = .m12 ∨ name = .m22 ∨ name = .m23 ∨ name = .m24)
    (he : Nonempty (D ≃* name.Carrier)) : False := by
  obtain ⟨e⟩ := he
  apply not_of_card_dvd_orderBound hA hB
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

/-- The native J₁ carrier has squarefree odd order. -/
theorem not_janko_one
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (he : Nonempty (D ≃* Janko1.Model)) : False := by
  obtain ⟨e⟩ := he
  apply not_of_card_dvd_orderBound hA hB
  rw [Nat.card_congr e.toEquiv, Janko1.card_model]
  norm_num

/-- The field-two symplectic derived row is the actual A₆ carrier. -/
theorem not_symplectic_derived
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (he : Nonempty (D ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) : False := by
  obtain ⟨e⟩ := he
  exact not_alternating hA hB 6 (by omega)
    ⟨e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩

/-- The actual binary G₂ derived group has order 6048. -/
theorem not_g2_derived
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (he : Nonempty (D ≃* commutator (Atlas.G2.Model (ZMod 2)))) : False := by
  obtain ⟨e⟩ := he
  apply not_of_card_dvd_orderBound hA hB
  rw [Nat.card_congr e.toEquiv, Atlas.G2.DerivedEvenOrder.card_derived_binary (Nat.card_zmod 2)]
  norm_num

/-- All binary rank-one rows are cyclic from the original permutability input. -/
theorem not_rank_one [Finite J]
    (hA : OddCartan.AmbientInput KnownSimple.IsKnownSimple D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (hna : ¬ IsMulCommutative D) (hm : IsBenderModel D) : False := by
  let : Fact p.Prime := ⟨hA.prime⟩
  let : IsSimpleGroup D := hA.simple
  have hcyc {n : ℕ} (hn : 1 < n) (hm : EvenActions.RankOne.IsBinaryRankOne D n) : False :=
    hB.oddComplement.not_isCyclic
      (EvenActions.RankOne.isCyclic_of_generalizedFitting D hA.fitting hna hn hm hA.large
        S B hA.p_group hA.inside hA.permutes)
  cases hm with
  | linear n hn hm => exact hcyc hn (Or.inl hm)
  | unitary n hn hm => exact hcyc hn (Or.inr (Or.inl hm))
  | suzuki m hm he => exact hcyc (n := 2*m+1) (by omega) (Or.inr (Or.inr ⟨m, rfl, he⟩))

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source
