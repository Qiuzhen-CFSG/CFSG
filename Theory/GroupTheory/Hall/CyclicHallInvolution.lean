module
public import Theory.GroupTheory.Hall.CyclicHallSmallIndex
public import Theory.GroupTheory.SolvableTwoFiveInvolution

/-!
# The fixed involution in a solvable group with cyclic odd Hall subgroup

If the two-core vanished, the odd core would lie in the cyclic Hall
subgroup. Its self-centralization would force every two-subgroup to be
abelian. Thus a nonabelian Sylow subgroup has nontrivial two-core. When
that Sylow has a unique involution, it is the unique involution of the
characteristic two-core and every automorphism fixes it.

The normal-intersection application retains a cyclic odd factor permuting
with the original Sylow subgroup. This supplies the involution fixed by
the Cartan actor in Aschbacher–Smith 5.1.13, printed p.636.
-/

public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Theory.GroupTheory.CyclicHallInvolution
variable {G : Type*} [Group G] [Finite G]

private theorem odd_normal_le_hall (D N : Subgroup G) [N.Normal]
    (hD : IsHallSubgroup OddHall.oddPrimes D) (hN : Odd (Nat.card N)) : N ≤ D := by
  have hcop : Nat.Coprime (Nat.card N) D.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpN hpD
    have hp2 : p = 2 := Classical.not_not.mp
      (hD.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hpD)
    exact hN.not_two_dvd_nat (hp2 ▸ hpN)
  have hd : D.relIndex N ∣ D.index := by
    rw [←relIndex_sup_of_normalizes N D le_normalizer_of_normal]
    exact relIndex_dvd_index_of_le le_sup_right
  exact relIndex_eq_one.mp
    (Nat.eq_one_of_dvd_coprimes hcop (relIndex_dvd_card D N) hd)

private theorem abelian_of_core_eq_bot
    (hs : Group.IsSolvable G) (D : Subgroup G) [IsCyclic D]
    (hD : IsHallSubgroup OddHall.oddPrimes D) (hc : pCore 2 G = ⊥)
    (P : Subgroup G) (hP : IsPGroup 2 P) : IsMulCommutative P := by
  have hOD : pPrimeCore 2 G ≤ D := odd_normal_le_hall D _ hD
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  let : IsCyclic (pPrimeCore 2 G) :=
    isCyclic_of_injective (inclusion hOD) (inclusion_injective hOD)
  have hd : _root_.commutator G ≤ pPrimeCore 2 G :=
    (commutator_le_centralizer_of_isCyclic_normal (pPrimeCore 2 G)).trans
      (centralizer_pPrimeCore_le_of_pCore_eq_bot 2 hs hc)
  have hcomm : ⁅P,P⁆ ≤ pPrimeCore 2 G :=
    (commutator_mono (show P ≤ ⊤ from le_top) le_top).trans hd
  have hdis : Disjoint P (pPrimeCore 2 G) := by
    obtain ⟨k,hk⟩ := hP.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact pPrimeCore_coprime_card.pow_left k
  exact commutator_self_eq_bot_iff.mp
    (le_bot_iff.mp ((le_inf (commutator_le_self P) hcomm).trans hdis.le_bot))

/-- Every automorphism fixes the unique involution of a nonabelian Sylow
when the solvable group has a cyclic odd Hall subgroup. -/
theorem fixed_involution
    (hs : Group.IsSolvable G) (D : Subgroup G) [IsCyclic D]
    (hD : IsHallSubgroup OddHall.oddPrimes D) (S : Sylow 2 G)
    (hna : ¬ IsMulCommutative S)
    (hu : ∀ x y : S, orderOf x = 2 → orderOf y = 2 → x = y)
    (z : S) (hz : orderOf z = 2) (φ : MulAut G) : φ z = z := by
  have hN : pCore 2 G ≠ ⊥ := fun he =>
    hna (abelian_of_core_eq_bot hs D hD he S S.isPGroup')
  have hc : 2 ∣ Nat.card (pCore 2 G) :=
    pCore_isPGroup.card_eq_or_dvd.resolve_left (fun he => hN (card_eq_one.mp he))
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := pCore 2 G) 2 hc
  have hNS : pCore 2 G ≤ (S : Subgroup G) := pCore_isPGroup.le_sylow_of_normal S
  have hxz : (x : G) = z := congrArg Subtype.val
    (hu ⟨x,hNS x.property⟩ z ((orderOf_coe _).symm.trans ((orderOf_coe x).trans hx)) hz)
  have hzN : (z : G) ∈ pCore 2 G := hxz ▸ x.property
  have hφN : φ (z : G) ∈ pCore 2 G :=
    characteristic_iff_le_comap.mp inferInstance φ hzN
  exact congrArg Subtype.val (hu ⟨φ z,hNS hφN⟩ z
    ((orderOf_coe _).symm.trans ((φ.orderOf_eq _).trans ((orderOf_coe z).trans hz))) hz)

/-- A cyclic odd actor fixes the unique involution in a nonabelian Sylow
intersection with the same normal subgroup. -/
theorem actor_fixes_involution
    (D C : Subgroup G) [IsCyclic D] [C.Normal] (P : Sylow 2 G)
    (ho : Odd (Nat.card D))
    (hp : (D : Set G) * (P : Set G) = (P : Set G) * (D : Set G))
    (hs : Group.IsSolvable (D ⊔ (P : Subgroup G) : Subgroup G))
    (S : Sylow 2 C) (hS : (S : Subgroup C) = (P : Subgroup G).subgroupOf C)
    (hna : ¬ IsMulCommutative S)
    (hu : ∀ x y : S, orderOf x = 2 → orderOf y = 2 → x = y)
    (z : S) (hz : orderOf z = 2) :
    D ≤ centralizer ({(z.val : G)} : Set G) := by
  let I := (D ⊔ (P : Subgroup G)) ⊓ C
  have hDI : D ≤ normalizer (I : Set G) :=
    (le_inf (le_sup_left.trans (D ⊔ (P : Subgroup G)).le_normalizer)
      le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  have hh := OddHall.hall_restrict_of_normalizes
    (CyclicHallSmallIndex.oddHall_of_permutes D P ho P.isPGroup' hp)
    (show D ≤ D ⊔ (P : Subgroup G) from le_sup_left) inf_le_left hDI
  let j : D.subgroupOf I →* D := I.subtype.subgroupComap D
  let : IsCyclic (D.subgroupOf I) := isCyclic_of_injective j (by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun d : D => (d : G)) he)))
  let : Group.IsSolvable (D ⊔ (P : Subgroup G) : Subgroup G) := hs
  let : Group.IsSolvable I := Group.isSolvable_of_isSolvable_injective
    (f := inclusion inf_le_left) (inclusion_injective inf_le_left)
  let J := (D ⊔ (P : Subgroup G)).subgroupOf C
  have hSJ : (S : Subgroup C) ≤ J := by rw [hS]; exact comap_mono le_sup_right
  let SJ := S.subtype hSJ
  let eJ : J ≃* I :=
    { toFun := fun x => ⟨x.val.val,x.property,x.val.property⟩
      invFun := fun x => ⟨⟨x.val,x.property.2⟩,x.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let SI := SJ.mapSurjective (f := eJ.toMonoidHom) eJ.surjective
  let eS : S ≃* SI := (subgroupOfEquivOfLe hSJ).symm.trans
    ((SJ : Subgroup J).equivMapOfInjective eJ.toMonoidHom eJ.injective)
  have hnaI : ¬ IsMulCommutative SI := by
    intro hi
    exact hna (IsMulCommutative.of_comm (fun a b => eS.injective (by
      rw [map_mul,map_mul,hi.is_comm.comm])))
  have huI (x y : SI) (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y :=
    eS.symm.injective (hu (eS.symm x) (eS.symm y)
      ((eS.symm.orderOf_eq x).trans hx) ((eS.symm.orderOf_eq y).trans hy))
  intro d hd
  let φ := MulAut.conjNormal (G := G) (H := C) d
  have hn : I.map (MulAut.conj d).toMonoidHom = I :=
    mem_normalizer_iff_map_conj_eq.mp (hDI hd)
  let ψ : MulAut I := (I.equivMapOfInjective (MulAut.conj d).toMonoidHom
    (MulAut.conj d).injective).trans (MulEquiv.subgroupCongr hn)
  have he := fixed_involution inferInstance (D.subgroupOf I) hh SI hnaI huI
    (eS z) ((eS.orderOf_eq z).trans hz) ψ
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp
    (congrArg (fun x : I => (x : G)) he))

end Theory.GroupTheory.CyclicHallInvolution
