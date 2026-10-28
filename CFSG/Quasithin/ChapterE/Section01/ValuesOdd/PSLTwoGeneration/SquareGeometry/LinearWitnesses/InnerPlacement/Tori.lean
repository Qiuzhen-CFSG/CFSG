module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LocalModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Sylow
public import GorensteinWalter.Section4.PSL2ReflectedTorusCard

/-!
# Dihedral witnesses through four-groups in prime-square PSL₂

Every involution centralizer in PSL₂(p²), for p odd, is a reflected cyclic
split torus. Given a four-group A containing the chosen involution z and
an odd prime r dividing the torus order, choose a reflector in A and an
element of order r in the torus. Together with z they generate an actual
dihedral subgroup of order 4r containing A.

If r does not divide the centralizer of z inside M, this subgroup escapes
M. Its order-four actor already forces the literal intersection with the
ambient Sylow to be Sylow in the subgroup. This replaces a uniform bound
on centralizers inside M, which is unavailable for subfield overgroups.
The choice of the missing prime is a separate geometric obligation.

The elementary reflection construction follows the private construction in
`PrimeGeometry.Diagonal.TorusWitness`, allowing any prescribed odd prime.
Source: Aschbacher--Smith, A.2.3(2), E.1.2 and E.1.14(6), printed pp.33,
209--210 and 214; Huppert II.8.3--4 for the actual reflected torus.
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement

private theorem reflected_prime_subgroup
    {G : Type*} [Group G] [Finite G]
    (U : Subgroup G) (hU : IsCyclic U) (s t : G)
    (hsU : s ∈ U) (hs : IsInvolution s)
    (htU : t ∉ U) (ht : t ^ 2 = 1)
    (hinv : ∀ x ∈ U, t * x * t⁻¹ = x⁻¹)
    {r : ℕ} (hr : r.Prime) (hro : Odd r) (hrU : r ∣ Nat.card U) :
    ∃ H : Subgroup G, s ∈ H ∧ t ∈ H ∧
      H ≤ U ⊔ zpowers t ∧ Nonempty (H ≃* DihedralGroup (2 * r)) := by
  let : IsCyclic U := hU
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := U) r hrU
  have huG : orderOf (u : G) = r := by simpa using hu
  have hsu : Commute s (u : G) := by
    exact congrArg Subtype.val (IsCyclic.isMulCommutative.is_comm.comm (⟨s, hsU⟩ : U) u)
  have hsord : orderOf s = 2 := orderOf_eq_prime hs.2 hs.1
  have hρord : orderOf (s * u) = 2 * r := by
    rw [hsu.orderOf_mul_eq_mul_orderOf_of_coprime]
    · rw [hsord, huG]
    · rw [hsord, huG]
      exact hro.coprime_two_left
  have hρpow : (s * (u : G)) ^ r = s := by
    rw [hsu.mul_pow, ← huG, pow_orderOf_eq_one, mul_one, huG]
    obtain ⟨k, hk⟩ := hro
    rw [hk, pow_add, pow_mul, hs.2, one_pow, pow_one, one_mul]
  let H : Subgroup G := zpowers (s * (u : G)) ⊔ zpowers t
  have hρU : s * (u : G) ∈ U := U.mul_mem hsU u.property
  have hρH : s * (u : G) ∈ H :=
    (le_sup_left : zpowers (s * (u : G)) ≤ H) (mem_zpowers _)
  have htH : t ∈ H := (le_sup_right : zpowers t ≤ H) (mem_zpowers _)
  let ρ : H := ⟨s * u, hρH⟩
  let σ : H := ⟨t, htH⟩
  have hgen : (⊤ : Subgroup H) = zpowers ρ ⊔ zpowers σ := by
    apply le_antisymm
    · intro x _
      have hx : (x : G) ∈ (zpowers ρ ⊔ zpowers σ).map H.subtype := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        exact x.property
      obtain ⟨y, hy, hyx⟩ := hx
      exact (Subtype.ext hyx : y = x) ▸ hy
    · exact le_top
  have hσ2 : σ ^ 2 = 1 := Subtype.ext ht
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := Subtype.ext (hinv _ hρU)
  have hσρ : σ ∉ zpowers ρ := by
    intro h
    apply htU
    obtain ⟨k, hk⟩ := h
    have hkG := congrArg Subtype.val hk
    change (s * (u : G)) ^ k = t at hkG
    rw [← hkG]
    exact U.zpow_mem hρU k
  have he := dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  have hord : orderOf ρ = 2 * r := by
    simpa only [ρ, Subgroup.orderOf_mk] using hρord
  rw [hord] at he
  refine ⟨H, ?_, htH, ?_, he⟩
  · exact hρpow ▸ H.pow_mem hρH r
  · exact sup_le_sup (zpowers_le.mpr hρU) le_rfl

private theorem kleinFour_le_of_pair
    {G : Type*} [Group G] [Finite G]
    (A H : Subgroup G) (hA : IsKleinFour A)
    {s t : G} (hsA : s ∈ A) (htA : t ∈ A)
    (hs1 : s ≠ 1) (ht1 : t ≠ 1) (hst : s ≠ t)
    (hsH : s ∈ H) (htH : t ∈ H) : A ≤ H := by
  classical
  let : IsKleinFour A := hA
  let : Fintype A := Fintype.ofFinite A
  have hall := IsKleinFour.eq_finset_univ
    (x := (⟨s, hsA⟩ : A)) (y := (⟨t, htA⟩ : A))
    (fun h => hs1 (congrArg Subtype.val h))
    (fun h => ht1 (congrArg Subtype.val h))
    (fun h => hst (congrArg Subtype.val h))
  intro x hx
  have hm : (⟨x, hx⟩ : A) ∈ ({⟨s, hsA⟩ * ⟨t, htA⟩, ⟨s, hsA⟩, ⟨t, htA⟩, 1} : Finset A) := by
    rw [hall]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h
  · have hx : x = s * t := congrArg Subtype.val h
    rw [hx]
    exact H.mul_mem hsH htH
  · have hx : x = s := congrArg Subtype.val h
    exact hx ▸ hsH
  · have hx : x = t := congrArg Subtype.val h
    exact hx ▸ htH
  · have hx : x = 1 := congrArg Subtype.val h
    exact hx ▸ H.one_mem

private theorem kleinFour_dihedral_in_reflected_torus
    {G : Type*} [Group G] [Finite G]
    (A U : Subgroup G) (hA : IsKleinFour A) (hU : IsCyclic U)
    (z w : G) (hzA : z ∈ A) (hzU : z ∈ U) (hz1 : z ≠ 1)
    (hwU : w ∉ U) (hw2 : w ^ 2 = 1)
    (hinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹)
    (hC : centralizer ({z} : Set G) = U ⊔ zpowers w)
    {r : ℕ} (hr : r.Prime) (hro : Odd r) (hrU : r ∣ Nat.card U) :
    ∃ H : Subgroup G, A ≤ H ∧ H ≤ centralizer ({z} : Set G) ∧
      Nonempty (H ≃* DihedralGroup (2 * r)) := by
  classical
  let : IsKleinFour A := hA
  let : IsCyclic U := hU
  have hAU : ¬ A ≤ U := fun h => hA.not_isCyclic (Subgroup.isCyclic_of_le h)
  obtain ⟨t, htA, htU⟩ := SetLike.not_le_iff_exists.mp hAU
  have ht1 : t ≠ 1 := fun h => htU (h ▸ U.one_mem)
  have hz2 : z ^ 2 = 1 := by
    rw [pow_two]
    exact congrArg Subtype.val (IsKleinFour.mul_self (⟨z, hzA⟩ : A))
  have ht2 : t ^ 2 = 1 := by
    rw [pow_two]
    exact congrArg Subtype.val (IsKleinFour.mul_self (⟨t, htA⟩ : A))
  have hAC : A ≤ centralizer ({z} : Set G) := by
    intro a ha
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm
      (⟨a, ha⟩ : A) ⟨z, hzA⟩)
  have htjoin : t ∈ U ⊔ zpowers w := hC ▸ hAC htA
  obtain ⟨u, hu, htu | htu⟩ :=
    (mem_sup_zpowers_of_involution_inverts hwU (by simpa only [pow_two] using hw2)
      hinv).mp htjoin
  · exact (htU (htu ▸ hu)).elim
  have htinv : ∀ x ∈ U, t * x * t⁻¹ = x⁻¹ := by
    intro x hx
    have hux : u * x⁻¹ = x⁻¹ * u := congrArg Subtype.val
      (IsCyclic.isMulCommutative.is_comm.comm (⟨u, hu⟩ : U) (⟨x, hx⟩ : U)⁻¹)
    calc
      t * x * t⁻¹ = u * (w * x * w⁻¹) * u⁻¹ := by rw [htu]; group
      _ = u * x⁻¹ * u⁻¹ := by rw [hinv x hx]
      _ = x⁻¹ := by rw [hux]; group
  obtain ⟨H, hzH, htH, hH, he⟩ :=
    reflected_prime_subgroup U hU z t hzU ⟨hz1, hz2⟩ htU ht2 htinv hr hro hrU
  refine ⟨H, kleinFour_le_of_pair A H hA hzA htA hz1 ht1
    (fun h => htU (h ▸ hzU)) hzH htH, ?_, he⟩
  apply hH.trans
  apply sup_le
  · rw [hC]
    exact le_sup_left
  · exact zpowers_le.mpr (hAC htA)

private theorem odd_square_half_succ {p : ℕ} (hp : Odd p) :
    Odd ((p ^ 2 + 1) / 2) := by
  obtain ⟨k, rfl⟩ := hp
  have he : (2 * k + 1) ^ 2 + 1 = 2 * (2 * (k * k + k) + 1) := by ring
  rw [he, Nat.mul_div_right]
  · exact ⟨k * k + k, rfl⟩
  · decide

/-- Every prescribed odd prime divisor of the involution torus produces
a dihedral subgroup through the whole four-group actor. -/
theorem dihedral_witness_of_torus_prime
    {F : Type*} [Field F] [Finite F] {p r : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hF : Nat.card F = p ^ 2)
    (A : Subgroup (PSL2 F)) (hA : IsKleinFour A)
    (z : PSL2 F) (hzA : z ∈ A) (hz1 : z ≠ 1)
    (hr : r.Prime) (hro : Odd r) (hrq : r ∣ (p ^ 2 - 1) / 2) :
    ∃ H : Subgroup (PSL2 F), A ≤ H ∧
      H ≤ centralizer ({z} : Set (PSL2 F)) ∧
      Nonempty (H ≃* DihedralGroup (2 * r)) := by
  let : IsKleinFour A := hA
  have hz2 : z ^ 2 = 1 := by
    rw [pow_two]
    exact congrArg Subtype.val (IsKleinFour.mul_self (⟨z, hzA⟩ : A))
  obtain ⟨U, w, hU, hzU, hw, hwU, hinv, hC, hUeven, hUcard⟩ :=
    psl2_reflected_torus_card (K := F) ⟨p, 2, hp, hodd, by decide, hF⟩ ⟨hz1, hz2⟩
  have hUc : Nat.card U = (p ^ 2 - 1) / 2 := by
    rcases hUcard with h | h
    · simpa only [hF] using h
    · have ho : Odd (Nat.card U) := by rw [h, hF]; exact odd_square_half_succ hodd
      exact (ho.not_two_dvd_nat hUeven.two_dvd).elim
  exact kleinFour_dihedral_in_reflected_torus A U hA hU z w hzA hzU hz1 hwU
    hw.2 hinv hC hr hro (hUc ▸ hrq)

/-- A prime absent from the centralizer inside M forces the constructed
dihedral local subgroup to escape M. -/
theorem local_witness_of_missing_centralizer_prime
    {F : Type*} [Field F] [Finite F] {p r : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hF : Nat.card F = p ^ 2)
    (T : Sylow 2 (PSL2 F)) (A M : Subgroup (PSL2 F))
    (hA : IsKleinFour A) (hAT : A ≤ (T : Subgroup (PSL2 F)))
    (z : PSL2 F) (hzA : z ∈ A) (hz1 : z ≠ 1)
    (hr : r.Prime) (hro : Odd r) (hrq : r ∣ (p ^ 2 - 1) / 2)
    (hrM : ¬ r ∣ Nat.card ((centralizer ({z} : Set (PSL2 F))).subgroupOf M)) :
    ∃ H : Subgroup (PSL2 F), A ≤ H ∧
      (∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup (PSL2 F)).subgroupOf H) ∧
      PrimeGeometry.LocalModel A H ∧ ¬ H ≤ M := by
  obtain ⟨H, hAH, hHC, ⟨eH⟩⟩ :=
    dihedral_witness_of_torus_prime hp hodd hF A hA z hzA hz1 hr hro hrq
  refine ⟨H, hAH, PrimeGeometry.Inner.sylow_intersection_dihedral
    T A H hAT hAH hA hro eH, Or.inr ⟨r, hr, hro, ⟨eH⟩⟩, ?_⟩
  intro hHM
  have hle : H.subgroupOf M ≤ (centralizer ({z} : Set (PSL2 F))).subgroupOf M :=
    fun x hx => hHC hx
  apply hrM
  have hc : Nat.card (H.subgroupOf M) = 4 * r := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hHM).toEquiv,
      Nat.card_congr eH.toEquiv, DihedralGroup.nat_card]
    ring
  exact (show r ∣ Nat.card (H.subgroupOf M) by rw [hc]; exact dvd_mul_left r 4).trans
    (card_dvd_of_le hle)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement

