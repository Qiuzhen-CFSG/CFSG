module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Normalizer.SevenCounts.FiberGeometry.Inversion

/-!
# The subgroup census in the seven-centralizer normalizer

Every subgroup of H = N_G(C_G(S)) of order dividing six embeds in the
cyclic quotient. A generator can therefore be conjugated into the fixed
complement by an element of A = C_G(S). Cyclic subgroup uniqueness and
fixed-point-free action show that every nontrivial subgroup of the complement
has exactly |A| distinct conjugates. This gives the counts for orders three
and six. Its centralizer in H is the complement itself; conjugating this
equality gives the literal order-three centralizer calculation.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), proof of (4.3), printed p.226.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
namespace BenderSevenStructure
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {h : Janko1CentralizerData G} {d : ℕ} (localData : BenderPrimeData G d)
    {S : Subgroup G} (hS : Nat.card S = 7) (structureData : BenderSevenStructure h S)

local notation "A" => centralizer (S : Set G)
local notation "H" => normalizer (A : Set G)
local notation "C" => (H ⊓ centralizer ({(structureData.t)} : Set G) : Subgroup G)

private theorem cyclic_mem_of_pow_card {F : Type*} [Group F] [Finite F] [IsCyclic F]
    (K : Subgroup F) {x : F} (hx : x ^ Nat.card K = 1) : x ∈ K := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hsub : (K : Set F).toFinset ⊆ Finset.univ.filter (fun a : F => a ^ Nat.card K = 1) := by
    intro a ha
    simp only [Set.mem_toFinset] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨a, ha⟩ : K)))
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    simpa [Set.toFinset_card, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
      using IsCyclic.card_pow_eq_one_le (α := F) (Nat.card_pos (α := K)))
  apply Set.mem_toFinset.mp
  rw [heq]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩

omit [IsSimpleGroup G] in
private theorem cyclic_subgroups_eq (K L D : Subgroup G) [IsCyclic D]
    (hK : K ≤ D) (hL : L ≤ D) (hcard : Nat.card K = Nat.card L) : K = L := by
  apply eq_of_le_of_card_ge ?_ hcard.ge
  intro x hx
  have hLcard : Nat.card (L.subgroupOf D) = Nat.card L :=
    Nat.card_congr (subgroupOfEquivOfLe hL).toEquiv
  apply cyclic_mem_of_pow_card (L.subgroupOf D) (x := ⟨x, hK hx⟩)
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, hLcard, ← hcard]
  exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : K)))

include localData hS structureData

/-- Subgroups of the normalizer whose orders divide six are cyclic. -/
public theorem fiber_small_subgroup_cyclic (K : Subgroup G) (hK : K ≤ H)
    (hcard : Nat.card K ∣ 6) : IsCyclic K := by
  apply (structureData.fiber_disjoint_cyclic localData hS K hK ?_).1
  exact disjoint_of_coprime_natCard
    (((h.seven_centralizer_coprime localData S hS).of_dvd_right
      (hcard.trans (by decide : 6 ∣ 120))).symm)

omit localData hS [IsSimpleGroup G] in
private theorem kernel_commuting_eq_one (a x : G) (ha : a ∈ A) (hx : x ∉ A)
    (hax : Commute a x) : a = 1 := by
  by_contra ha1
  apply hx
  rw [← structureData.centralizers a ha ha1]
  exact mem_centralizer_singleton_iff.mpr hax.symm.eq

omit localData hS [IsSimpleGroup G] in
private theorem complement_commute (x y : G) (hx : x ∈ C) (hy : y ∈ C) :
    Commute x y := by
  let _ : IsCyclic C := structureData.complement_cyclic
  let _ : CommGroup C := IsCyclic.commGroup
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : C) ⟨y, hy⟩)

private theorem kernel_conjugate_complement (a x : G) (ha : a ∈ A)
    (hx : x ∈ C) (hx1 : x ≠ 1) (hax : a * x * a⁻¹ ∈ C) : a = 1 := by
  have hk : (a * x * a⁻¹) * x⁻¹ ∈ A := by
    have hh : x * a⁻¹ * x⁻¹ ∈ A :=
      (mem_normalizer_iff.mp hx.1 a⁻¹).mp (inv_mem ha)
    simpa only [mul_assoc] using mul_mem ha hh
  have he : (a * x * a⁻¹) * x⁻¹ = 1 :=
    (structureData.kernel_disjoint_complement localData hS).le_bot
      ⟨hk, (C).mul_mem hax ((C).inv_mem hx)⟩
  have hc : Commute a x := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp he)
  have hxA : x ∉ A := fun hxA => hx1
    ((structureData.kernel_disjoint_complement localData hS).le_bot ⟨hxA, hx⟩)
  exact structureData.kernel_commuting_eq_one a x ha hxA hc

/-- Subgroups of the same nontrivial order are conjugate into the literal cyclic complement by the kernel. -/
public theorem fiber_subgroup_conjugate (D K : Subgroup G) (hDC : D ≤ C)
    (hn : 1 < Nat.card D) (hKH : K ≤ H) (hcard : Nat.card K = Nat.card D) :
    ∃ a ∈ A, K = D.map (MulAut.conj a).toMonoidHom := by
  have hdiv : Nat.card K ∣ 6 := by
    rw [hcard, ← structureData.complement_card]
    exact card_dvd_of_le hDC
  let _ : IsCyclic K := structureData.fiber_small_subgroup_cyclic localData hS K hKH hdiv
  obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := K)
  have hxG : orderOf (x : G) = Nat.card K :=
    (orderOf_injective K.subtype K.subtype_injective x).trans hx
  have hx1 : (x : G) ≠ 1 := by
    intro he
    rw [he, orderOf_one, hcard] at hxG
    omega
  have hdisj : Disjoint K A := disjoint_of_coprime_natCard
    (((h.seven_centralizer_coprime localData S hS).of_dvd_right
      (hdiv.trans (by decide : 6 ∣ 120))).symm)
  have hxA : (x : G) ∉ A := fun hh => hx1 (hdisj.le_bot ⟨x.2, hh⟩)
  obtain ⟨a, ha, c, hc, he⟩ := structureData.conjugate_into_complement x (hKH x.2) hxA
  have hxc : (MulAut.conj a) c = (x : G) := he.symm
  have hcorder : orderOf c = Nat.card D := by
    rw [← (MulAut.conj a).orderOf_eq c, hxc, hxG, hcard]
  have hKD : zpowers c = D := by
    let _ : IsCyclic C := structureData.complement_cyclic
    apply cyclic_subgroups_eq _ _ C (zpowers_le.mpr hc) hDC
    rw [Nat.card_zpowers, hcorder]
  have hKx : zpowers (x : G) = K :=
    eq_of_le_of_card_ge (zpowers_le.mpr x.2) (by rw [Nat.card_zpowers, hxG])
  refine ⟨a, ha, ?_⟩
  rw [← hKD, MonoidHom.map_zpowers]
  change K = zpowers ((MulAut.conj a) c)
  rw [hxc, hKx]

/-- Distinct kernel elements give distinct conjugates of each nontrivial complement subgroup. -/
public theorem fiber_conjugates_injective (D : Subgroup G) (hDC : D ≤ C)
    (hn : 1 < Nat.card D) :
    Function.Injective (fun a : A => D.map (MulAut.conj (a : G)).toMonoidHom) := by
  intro a b hab
  dsimp only at hab
  let _ : Nontrivial D := D.nontrivial_iff_ne_bot.mpr (D.one_lt_card_iff_ne_bot.mp hn)
  obtain ⟨x, hx1⟩ := exists_ne (1 : D)
  have hxG1 : (x : G) ≠ 1 := fun hh => hx1 (Subtype.ext hh)
  have hax : (MulAut.conj (a : G)) x ∈ D.map (MulAut.conj (b : G)).toMonoidHom := by
    rw [← hab]
    exact mem_map.mpr ⟨x, x.2, rfl⟩
  have hax' : (b : G)⁻¹ * (a * x * (a : G)⁻¹) * b ∈ D := by
    exact mem_map_equiv.mp hax
  have hconj : ((b : G)⁻¹ * a) * x * ((b : G)⁻¹ * a)⁻¹ ∈ C := by
    have hh := hDC hax'
    convert hh using 1
    group
  have he := structureData.kernel_conjugate_complement localData hS
    ((b : G)⁻¹ * a) x (mul_mem (inv_mem b.2) a.2) (hDC x.2) hxG1 hconj
  exact Subtype.ext (inv_mul_eq_one.mp he).symm

/-- Every nontrivial subgroup order in the complement has exactly one conjugate per kernel element. -/
public theorem fiber_subgroups_card (D : Subgroup G) (hDC : D ≤ C)
    (hn : 1 < Nat.card D) :
    Nat.card (BenderSubgroupsOfOrder H (Nat.card D)) = Nat.card A := by
  let f : A → BenderSubgroupsOfOrder H (Nat.card D) := fun a =>
    ⟨D.map (MulAut.conj (a : G)).toMonoidHom, (by
      rintro x ⟨y, hy, rfl⟩
      exact (H).mul_mem ((H).mul_mem (le_normalizer a.2) (hDC hy).1)
        ((H).inv_mem (le_normalizer a.2))),
      card_map_of_injective (MulAut.conj (a : G)).injective⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact structureData.fiber_conjugates_injective localData hS D hDC hn
        (congrArg Subtype.val hab)
    · intro K
      obtain ⟨a, ha, he⟩ := structureData.fiber_subgroup_conjugate localData hS
        D K.1 hDC hn K.2.1 K.2.2
      exact ⟨⟨a, ha⟩, Subtype.ext he.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

private theorem complement_subgroup_centralizer (D : Subgroup G) (hDC : D ≤ C)
    (hn : 1 < Nat.card D) : H ⊓ centralizer (D : Set G) = C := by
  apply le_antisymm
  · intro y hy
    obtain ⟨a, ha, c, hc, he⟩ := structureData.factorization y hy.1
    let _ : Nontrivial D := D.nontrivial_iff_ne_bot.mpr (D.one_lt_card_iff_ne_bot.mp hn)
    obtain ⟨x, hx1⟩ := exists_ne (1 : D)
    have hxG1 : (x : G) ≠ 1 := fun hh => hx1 (Subtype.ext hh)
    have hxA : (x : G) ∉ A := fun hxA => hxG1
      ((structureData.kernel_disjoint_complement localData hS).le_bot ⟨hxA, hDC x.2⟩)
    have hcx := structureData.complement_commute c x hc (hDC x.2)
    have hxy : (x : G) * y = y * x := hy.2 x x.2
    have hax : Commute a (x : G) := by
      apply mul_right_cancel (b := c)
      calc
        a * x * c = a * (c * x) := by rw [mul_assoc, hcx.eq]
        _ = x * a * c := by rw [← mul_assoc, ← he, ← hxy, he, mul_assoc]
    have ha1 := structureData.kernel_commuting_eq_one a x ha hxA hax
    simpa only [he, ha1, one_mul] using hc
  · intro y hy
    refine ⟨hy.1, ?_⟩
    intro x hx
    exact (structureData.complement_commute x y (hDC hx) hy).eq

private theorem conjugate_subgroup_centralizer (D : Subgroup G) (hDC : D ≤ C)
    (hn : 1 < Nat.card D) (a : G) (ha : a ∈ A) :
    H ⊓ centralizer (D.map (MulAut.conj a).toMonoidHom : Set G) =
      (C).map (MulAut.conj a).toMonoidHom := by
  let e := MulAut.conj a
  have haH : a ∈ H := le_normalizer ha
  have hbase := structureData.complement_subgroup_centralizer localData hS D hDC hn
  ext y
  rw [mem_map_equiv]
  constructor
  · intro hy
    have hh : e.symm y ∈ H ⊓ centralizer (D : Set G) := by
      refine ⟨(H).mul_mem ((H).mul_mem ((H).inv_mem haH) hy.1) haH, ?_⟩
      intro z hz
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hy.2 (e z) (mem_map.mpr ⟨z, hz, rfl⟩)
    exact hbase ▸ hh
  · intro hy
    have hh : e.symm y ∈ H ⊓ centralizer (D : Set G) := hbase.symm ▸ hy
    have hyH : y ∈ H := by
      have h0 := (H).mul_mem ((H).mul_mem haH hh.1) ((H).inv_mem haH)
      change e (e.symm y) ∈ H at h0
      simpa only [MulEquiv.apply_symm_apply] using h0
    refine ⟨hyH, ?_⟩
    rintro z ⟨w, hw, rfl⟩
    have heq := congrArg e (hh.2 w hw)
    change e w * y = y * e w
    simpa only [map_mul, MulEquiv.apply_symm_apply] using heq

/-- The centralizer in H of any nontrivial subgroup conjugate into the complement has order six. -/
public theorem fiber_centralizer_card (D K : Subgroup G) (hDC : D ≤ C)
    (hn : 1 < Nat.card D) (hKH : K ≤ H) (hcard : Nat.card K = Nat.card D) :
    Nat.card (H ⊓ centralizer (K : Set G) : Subgroup G) = 6 := by
  obtain ⟨a, ha, he⟩ := structureData.fiber_subgroup_conjugate localData hS D K hDC hn hKH hcard
  rw [he, structureData.conjugate_subgroup_centralizer localData hS D hDC hn a ha,
    card_map_of_injective (MulAut.conj a).injective, structureData.complement_card]

omit localData hS [IsSimpleGroup G] in
private theorem complement_three : ∃ D : Subgroup G, D ≤ C ∧ Nat.card D = 3 := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := C) 3
    (by rw [structureData.complement_card]; decide)
  refine ⟨zpowers (x : G), zpowers_le.mpr x.2, ?_⟩
  rw [Nat.card_zpowers]
  exact (orderOf_injective (C).subtype (C).subtype_injective x).trans hx

/-- The normalizer has exactly |A| subgroups of order three. -/
public theorem fiber_three_subgroups : Nat.card (BenderSubgroupsOfOrder H 3) = Nat.card A := by
  obtain ⟨D, hD, hc⟩ := structureData.complement_three
  have he := structureData.fiber_subgroups_card localData hS D hD (by omega)
  rwa [hc] at he

/-- The normalizer has exactly |A| subgroups of order six. -/
public theorem fiber_six_subgroups : Nat.card (BenderSubgroupsOfOrder H 6) = Nat.card A := by
  have he := structureData.fiber_subgroups_card localData hS C le_rfl
    (by rw [structureData.complement_card]; decide)
  rwa [structureData.complement_card] at he

/-- The literal centralizer in H of each order-three subgroup has order six. -/
public theorem fiber_three_centralizer (K : Subgroup G) (hK : K ≤ H) (hc : Nat.card K = 3) :
    Nat.card (H ⊓ centralizer (K : Set G) : Subgroup G) = 6 := by
  obtain ⟨D, hD, hDc⟩ := structureData.complement_three
  exact structureData.fiber_centralizer_card localData hS D K hD (by omega) hK (hc.trans hDc.symm)

end BenderSevenStructure
end CFSG.Quasithin.Janko1CentralizerData
