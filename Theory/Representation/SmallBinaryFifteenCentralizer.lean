module
public import Theory.Representation.SmallBinaryFiveOvergroup

/-!
# Cubic centralizers forced by a normal cyclic fifteen

In a faithful binary four-dimensional action, a nontrivial involution cannot
centralize an order-five subgroup: that subgroup has odd centralizer. If its
centralizer also has no factor three, its action on a normal cyclic fifteen
is fixed-point-free and therefore inversion. The order-fifteen action theorem
excludes this inversion on sixteen vectors.

Source application: Aschbacher--Smith 15.2.13, printed pp.1111--1112,
refs/quasithin.pdf. The normal subgroup and representation are literal.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Representation.SmallBinaryFiveOvergroup
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- A normal cyclic fifteen forces a cubic subgroup in every involution centralizer. -/
theorem three_dvd_involution_centralizer_of_normal_fifteen
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (h4 : Module.finrank (ZMod 2) W = 4)
    (F : Subgroup D) [F.Normal] (he : Nonempty (F ≃* Multiplicative (ZMod 15)))
    (t : D) (ht : t ^ 2 = 1) (htne : t ≠ 1) :
    3 ∣ Nat.card (centralizer ({t} : Set D)) := by
  by_contra hthree
  obtain ⟨e⟩ := he
  let : IsCyclic F := isCyclic_of_injective e.toMonoidHom e.injective
  have hF : Nat.card F = 15 := (Nat.card_congr e.toEquiv).trans (by simp)
  let C := F ⊓ centralizer ({t} : Set D)
  have hCdiv : Nat.card C ∣ 15 := hF ▸ card_dvd_of_le (show C ≤ F from inf_le_left)
  have hCthree : ¬ 3 ∣ Nat.card C := fun hd =>
    hthree (hd.trans (card_dvd_of_le (show C ≤ centralizer {t} from inf_le_right)))
  have hCfive : ¬ 5 ∣ Nat.card C := by
    intro hd
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 5 hd
    have hpc : Nat.card (zpowers (c : D)) = 5 := by
      rw [Nat.card_zpowers,orderOf_coe,hc]
    have hct : t ∈ centralizer (zpowers (c : D) : Set D) := by
      intro y hy
      obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hy
      have hcomm : Commute (c : D) t := mem_centralizer_singleton_iff.mp c.property.2
      exact (hcomm.zpow_left n).eq
    have htd : 2 ∣ Nat.card (centralizer (zpowers (c : D) : Set D)) := by
      have ho : orderOf (⟨t,hct⟩ : centralizer (zpowers (c : D) : Set D)) = 2 := by
        rw [←orderOf_coe]
        exact orderOf_eq_prime ht htne
      exact ho ▸ orderOf_dvd_natCard (⟨t,hct⟩ : centralizer (zpowers (c : D) : Set D))
    exact (by decide : ¬ 2 ∣ 15) (htd.trans (centralizer_card_dvd ρ hf h4 _ hpc))
  have hCcard : Nat.card C = 1 := by
    have hh := Nat.mem_divisors.mpr ⟨hCdiv,by decide⟩
    rw [show Nat.divisors 15 = {1,3,5,15} by decide] at hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with hh | hh | hh | hh
    · exact hh
    · exact (hCthree (by rw [hh])).elim
    · exact (hCfive (by rw [hh])).elim
    · exact (hCthree (by rw [hh]; decide)).elim
  have hCb : C = ⊥ := eq_bot_of_card_eq _ hCcard
  let φ : MulAut F := MulAut.conjNormal t
  have hfree : MonoidHom.FixedPointFree φ := by
    intro x hx
    apply Subtype.ext
    have hxv : t * (x : D) * t⁻¹ = x := congrArg Subtype.val hx
    have hxc : (x : D) ∈ C := ⟨x.property, by
      change (x : D) ∈ centralizer {t}
      rw [mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp hxv).symm⟩
    exact mem_bot.mp (hCb ▸ hxc)
  have hφ2 : φ ^ 2 = 1 := by
    change (MulAut.conjNormal : D →* MulAut F) t ^ 2 = 1
    rw [←map_pow,ht,map_one]
  have hinv := hfree.coe_eq_inv_of_involutive
    (fun x => congrArg (fun f : MulAut F => f x) hφ2)
  obtain ⟨a,ha⟩ := IsCyclic.exists_generator (α := F)
  have hao : orderOf (a : D) = 15 := (orderOf_coe a).trans
    ((orderOf_eq_card_of_forall_mem_zpowers ha).trans hF)
  let := BinaryGroupAction.action ρ
  let := BinaryGroupAction.faithful ρ hf
  let := BinaryGroupAction.elementary (V := W)
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let f := MulDistribMulAction.toMulAut D (Multiplicative W)
  have hfi : Function.Injective f := by
    intro x y hh
    exact FaithfulSMul.eq_of_smul_eq_smul (α := Multiplicative W)
      (fun v => congrArg (fun z : MulAut (Multiplicative W) => z v) hh)
  have hW : Nat.card (Multiplicative W) = 16 := by
    change Nat.card W = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,h4]
    rfl
  apply MulAut.not_inverts_order_fifteen_on_sixteen hW (f a) (f t)
    ((orderOf_injective f hfi _).trans hao) (by rw [←map_pow,ht,map_one])
  have hh : t * (a : D) * t⁻¹ = (a : D)⁻¹ :=
    congrArg Subtype.val (congrFun hinv a)
  simpa only [map_mul,map_inv] using congrArg f hh
end Representation.SmallBinaryFiveOvergroup
