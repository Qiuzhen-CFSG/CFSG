module
public import Theory.SpecificGroups.ThreeDivisibility.Sporadic
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M23.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.SpecificGroups.Janko1.Model.Basic
public import Theory.SpecificGroups.Janko3.Model.Basic
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates
public import Theory.SpecificGroups.Lyons.Atlas111WordRelations
public import Theory.SpecificGroups.HaradaNorton.Order.LocalCard
public import Theory.SpecificGroups.ONan.E9A4.Embedding
public import Theory.SpecificGroups.Monster.Construction.QuasithinObstruction
public import Theory.GroupTheory.PrimeRankZero

/-!
# Small prime divisors in concrete sporadic carriers

The Mathieu orders, certified generator words for J₁, J₃, Th and Ly, the
actual A₁₂ subgroup of HN, and the E₉×A₄ embedding into O’Nan supply a
factor three or five. The Monster uses its actual local projection to the
lattice Conway quotient and that quotient’s proved three-rank lower bound.
No full-order or simplicity certificate is used where these smaller witnesses
suffice. Source data and attribution are retained by the imported carriers.
-/

public section
namespace Theory.SpecificGroups.PrimeToFifteen
theorem m11 : 3 ∣ Nat.card Sporadic.Mathieu.M11 := by rw [Sporadic.Mathieu.m11_order]; norm_num
theorem m12 : 3 ∣ Nat.card Sporadic.Mathieu.M12 := by rw [Sporadic.Mathieu.m12_order]; norm_num
theorem m22 : 3 ∣ Nat.card Sporadic.Mathieu.M22 := by rw [Sporadic.Mathieu.m22_order]; norm_num
theorem m23 : 3 ∣ Nat.card Sporadic.Mathieu.M23 := by rw [Sporadic.Mathieu.m23_order]; norm_num
theorem m24 : 3 ∣ Nat.card Sporadic.Mathieu.M24 := by rw [Sporadic.Mathieu.m24_order]; norm_num

theorem j1 : 3 ∣ Nat.card Janko1.Model := Janko1.orderOf_b ▸ orderOf_dvd_natCard _

theorem j3 : 3 ∣ Nat.card Sporadic.Janko3.Model := by
  have hb : Sporadic.Janko3.b ≠ 1 := by
    intro h
    exact Sporadic.Janko3.a_mul_b_ne_b_mul_a (by simp [h])
  exact (show orderOf Sporadic.Janko3.b = 3 from
    orderOf_eq_prime Sporadic.Janko3.b_cube hb) ▸ orderOf_dvd_natCard _

theorem thompson : 3 ∣ Nat.card Thompson.Model := by
  have hb : Thompson.generatorB ≠ 1 := by
    intro h
    exact Thompson.generator_mul_ne (by simp [h])
  exact (show orderOf Thompson.generatorB = 3 from
    orderOf_eq_prime Thompson.generatorB_cube hb) ▸ orderOf_dvd_natCard _

theorem lyons : 5 ∣ Nat.card Lyons.LyonsGroup := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hb : Lyons.generatorB ≠ 1 := by
    intro h
    exact Lyons.generators_not_commute (by simp [h])
  exact (show orderOf Lyons.generatorB = 5 from
    orderOf_eq_prime Lyons.SimplicityCertificate.generatorB_pow_five hb) ▸ orderOf_dvd_natCard _

theorem haradaNorton : 3 ∣ Nat.card HaradaNorton.HN :=
  (show 3 ∣ Nat.card HaradaNorton.OrderCertificate.localSubgroup by rw [HaradaNorton.OrderCertificate.localSubgroup_card]; norm_num).trans
    HaradaNorton.OrderCertificate.localSubgroup.card_subgroup_dvd_card

theorem onan : 3 ∣ Nat.card ONan.Model := by
  have hd : 3 ∣ Nat.card Theory.SpecificGroups.E9A4.Source := by
    change 3 ∣ Nat.card (Multiplicative (ZMod 3 × ZMod 3) × alternatingGroup (Fin 4))
    rw [Nat.card_prod]
    apply dvd_mul_of_dvd_left
    change 3 ∣ Nat.card (ZMod 3 × ZMod 3)
    norm_num [Nat.card_prod]
  exact hd.trans (Subgroup.card_dvd_of_injective ONan.E9A4.embedding ONan.E9A4.embedding_injective)

theorem monster [Finite Sporadic.Monster.GriessGroup] :
    3 ∣ Nat.card Sporadic.Monster.GriessGroup := by
  open Sporadic.Monster.Construction.QuasithinObstruction in
  have hd : 3 ∣ Nat.card Atlas.Conway.LeechCentralQuotient := by
    by_contra hn
    have hr := PrimeRank.eq_zero_iff_not_dvd_card.mpr hn
    have hle := leechCentralQuotient_three_le_primeRank
    omega
  exact hd.trans ((Subgroup.card_dvd_of_surjective
    Sporadic.Monster.Construction.QuasithinObstruction.localToLeechQuotient
    Sporadic.Monster.Construction.QuasithinObstruction.localToLeechQuotient_surjective).trans
    Sporadic.Monster.Construction.localSubgroup.card_subgroup_dvd_card)

end Theory.SpecificGroups.PrimeToFifteen
