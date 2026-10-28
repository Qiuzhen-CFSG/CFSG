module
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.HeldBounds
public import Theory.SpecificGroups.Held.Model.FourPointBase
public import Theory.GroupTheory.CentralExtensionPartialInversion
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Five-primary kernels over Held

Three conjugates of the original involutory generator supply explicit
commuting elements of order five and an element inverting the first while
fixing the second. Their cyclic subgroups intersect trivially, so their join
has order 25 and is Sylow by the proved ambient odd-order bound. Partial
inversion forces commuting lifts and excludes five from every finite
perfect central kernel. All word identities are checked on the concrete
four-point base. Source: Aschbacher–Smith I.1.3, printed p.407; the original
ATLAS HeG1-p2058B0 model.
-/

open Subgroup
namespace Held.OddPrimary

private def fiveWord (is : List (Fin 3)) : He :=
  (is.map (fun i => (![a, b ^ (-2 : ℤ) * a * b ^ 2,
    b ^ 2 * a * b ^ (-2 : ℤ)] : Fin 3 → He) i)).prod
private def fiveActor : He := fiveWord [1,2,1,2,0,1,2,1,0,2,1,2,1,0,2,1,2,0]
private def fiveFirst : He := fiveWord [1,2,0,1,0,2,1,0,1,2,1,2,0,2,1,0,1]
private def fiveSecond : He := fiveWord [2,0,1,2,0,1,2,1,0,2,1,2,0,2,0,1,0,2,1,2]

private theorem five_first_pow : fiveFirst ^ 5 = 1 := by
  apply eq_of_four_point_images
  decide +kernel
private theorem five_second_pow : fiveSecond ^ 5 = 1 := by
  apply eq_of_four_point_images
  decide +kernel
private theorem five_first_ne : fiveFirst ≠ 1 := by
  have hn : representation fiveFirst 0 ≠ 0 := by decide +kernel
  exact fun h => hn (congrArg (fun g : He => representation g 0) h)
private theorem five_second_ne : fiveSecond ≠ 1 := by
  have hn : representation fiveSecond 0 ≠ 0 := by decide +kernel
  exact fun h => hn (congrArg (fun g : He => representation g 0) h)
private theorem five_comm : Commute fiveFirst fiveSecond := by
  change fiveFirst * fiveSecond = fiveSecond * fiveFirst
  apply eq_of_four_point_images
  decide +kernel
private theorem five_actor_first : fiveActor * fiveFirst * fiveActor⁻¹ = fiveFirst⁻¹ := by
  apply eq_of_four_point_images
  decide +kernel
private theorem five_actor_second : Commute fiveActor fiveSecond := by
  change fiveActor * fiveSecond = fiveSecond * fiveActor
  apply eq_of_four_point_images
  decide +kernel

private theorem five_disjoint : Disjoint (zpowers fiveFirst) (zpowers fiveSecond) := by
  apply disjoint_def.mpr
  intro g hg hh
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hg
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hh
  have hf : fiveActor * g * fiveActor⁻¹ = g := by
    rw [← hj, (five_actor_second.zpow_right j).eq, mul_inv_cancel_right]
  have hn : fiveActor * g * fiveActor⁻¹ = g⁻¹ := by
    rw [← hi, ← conj_zpow, five_actor_first, inv_zpow]
  have h2 : g ^ 2 = 1 := by
    rw [pow_two]
    calc g * g = g⁻¹ * g := congrArg (fun a => a * g) (hf.symm.trans hn)
         _ = 1 := inv_mul_cancel _
  have h5 : g ^ 5 = 1 := by
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, five_first_pow, one_zpow]
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 5 2)
    (orderOf_dvd_of_pow_eq_one h5) (orderOf_dvd_of_pow_eq_one h2))

public theorem exists_five_configuration :
    ∃ (Q : Sylow 5 He) (x y r : He),
      closure ({x, y} : Set He) = (Q : Subgroup He) ∧
      x ^ 5 = 1 ∧ Commute x y ∧
      r * x * r⁻¹ = x⁻¹ ∧ Commute r y := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P := closure ({fiveFirst, fiveSecond} : Set He)
  have hP : P = zpowers fiveFirst ⊔ zpowers fiveSecond := by
    rw [zpowers_eq_closure, zpowers_eq_closure, ← closure_union]
    rfl
  have hn : zpowers fiveSecond ≤ normalizer (zpowers fiveFirst : Set He) := by
    apply le_trans _ (centralizer_le_normalizer _)
    apply zpowers_le.mpr
    intro g hg
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hg
    exact (five_comm.zpow_left i).eq
  have hc : Nat.card P = 5 ^ 2 := by
    rw [hP, card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn five_disjoint,
      Nat.card_zpowers, Nat.card_zpowers,
      orderOf_eq_prime five_first_pow five_first_ne,
      orderOf_eq_prime five_second_pow five_second_ne]
    norm_num
  have hp : IsPGroup 5 P := IsPGroup.of_card (n := 2) hc
  have hi := not_dvd_index_of_card P hc (by decide)
  exact ⟨hp.toSylow hi, fiveFirst, fiveSecond, fiveActor, rfl,
    five_first_pow, five_comm, five_actor_first, five_actor_second⟩

public theorem not_five_dvd_card_kernel
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* He) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ¬5 ∣ Nat.card f.ker := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨Q, x, y, r, hQ, hx, hxy, hrx, hry⟩ := exists_five_configuration
  exact CentralExtension.not_dvd_card_kernel_of_partial_inversion
    f hf hk Q x y r hQ (by decide : Nat.Coprime 5 2) hx hxy hrx hry

end Held.OddPrimary
