module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.Tori
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner.Overgroups.Models
public import GorensteinWalter.PGL2InnerAction

/-!
# Centralizers of inner involutions in PGL₂(p)

Every four-group meets the index-two PSL₂ subgroup nontrivially. The
centralizer of such an involution in PSL₂ is a reflected cyclic torus;
its cardinality is p-1 or p+1, with the even torus half selecting the sign.
Normality and index divisibility show that its PGL₂ centralizer order
divides twice that cardinality. This divisibility suffices for the missing
prime argument, without another projective matrix centralizer calculation.

All transfers retain the actual image of the chosen involution, including
the literal ambient centralizer restricted to the original overgroup.
Source: Huppert II.8.3--4 and the prime-square calculation for
Aschbacher--Smith E.1.14(6), printed p.214 (citing Asc82a, Lemma 4.10).
-/

public section

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.CentralizerPrimes

private theorem centralizer_card_equiv {G K : Type*} [Group G] [Group K]
    (e : G ≃* K) (z : G) :
    Nat.card (centralizer ({z} : Set G)) =
      Nat.card (centralizer ({e z} : Set K)) := by
  have heq : (centralizer ({z} : Set G)).map e.toMonoidHom =
      centralizer ({e z} : Set K) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change y ∈ centralizer ({z} : Set G) at hy
      rw [mem_centralizer_singleton_iff] at hy ⊢
      simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e hy
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      change e.symm x ∈ centralizer ({z} : Set G)
      rw [mem_centralizer_singleton_iff] at hx ⊢
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using hx
  rw [← heq, card_map_of_injective e.injective]

private theorem relative_centralizer_eq {G : Type*} [Group G]
    (M : Subgroup G) (z : M) :
    (centralizer ({(z : G)} : Set G)).subgroupOf M = centralizer ({z} : Set M) := by
  ext x
  simp only [mem_subgroupOf, mem_centralizer_singleton_iff]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- Cardinality transport for the literal centralizer in an ambient overgroup. -/
theorem relative_centralizer_card_equiv {G K : Type*} [Group G] [Group K]
    (M : Subgroup G) (e : M ≃* K) (z : M) :
    Nat.card ((centralizer ({(z : G)} : Set G)).subgroupOf M) =
      Nat.card (centralizer ({e z} : Set K)) := by
  rw [relative_centralizer_eq]
  exact centralizer_card_equiv e z

private theorem subgroupOf_card_swap {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card (H.subgroupOf K) = Nat.card (K.subgroupOf H) := by
  exact Nat.card_congr
    { toFun := fun x => ⟨⟨x, x.property⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x, x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem centralizer_card_dvd_index_two {G : Type*} [Group G]
    (N : Subgroup G) (hN : N.index = 2) (z : N) :
    Nat.card (centralizer ({(z : G)} : Set G)) ∣
      2 * Nat.card (centralizer ({z} : Set N)) := by
  let : N.Normal := normal_of_index_eq_two hN
  let C := centralizer ({(z : G)} : Set G)
  have hd : (N.subgroupOf C).index ∣ 2 := by
    simpa only [Subgroup.relIndex, hN] using N.relIndex_dvd_index_of_normal C
  have hc : Nat.card (N.subgroupOf C) = Nat.card (centralizer ({z} : Set N)) := by
    rw [subgroupOf_card_swap, relative_centralizer_eq]
  have hh := Nat.mul_dvd_mul_right hd (Nat.card (N.subgroupOf C))
  rwa [(N.subgroupOf C).index_mul_card, hc] at hh

private theorem kleinFour_meets_index_two {G : Type*} [Group G]
    (A N : Subgroup G) (hA : IsKleinFour A) (hN : N.index = 2) :
    ∃ z : G, z ∈ A ∧ z ∈ N ∧ z ≠ 1 := by
  let : N.Normal := normal_of_index_eq_two hN
  have hne : A ⊓ N ≠ ⊥ := by
    intro hbot
    have hd := N.relIndex_dvd_index_of_normal A
    rw [← inf_relIndex_right, inf_comm, hbot, relIndex_bot_left, hN, hA.card_four] at hd
    norm_num at hd
  obtain ⟨z, hz, hz1⟩ := (A ⊓ N).bot_or_exists_ne_one.resolve_left hne
  exact ⟨z, hz.1, hz.2, hz1⟩

private theorem reflected_join_card {G : Type*} [Group G] [Finite G]
    (U : Subgroup G) (hU : IsCyclic U) (w : G) (hwU : w ∉ U)
    (hw2 : w ^ 2 = 1) (hinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹) :
    Nat.card (U ⊔ zpowers w : Subgroup G) = 2 * Nat.card U := by
  obtain ⟨r, hr⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top U).mp hU
  have hrU : r ∈ U := hr ▸ mem_zpowers r
  let D : Subgroup G := U ⊔ zpowers w
  let ρ : D := ⟨r, (le_sup_left : U ≤ D) hrU⟩
  let σ : D := ⟨w, (le_sup_right : zpowers w ≤ D) (mem_zpowers w)⟩
  have hgen : (⊤ : Subgroup D) = zpowers ρ ⊔ zpowers σ := by
    apply le_antisymm
    · intro x _
      have hx : (x : G) ∈ (zpowers ρ ⊔ zpowers σ).map D.subtype := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        change (x : G) ∈ zpowers r ⊔ zpowers w
        rw [hr]
        exact x.property
      obtain ⟨y, hy, hyx⟩ := hx
      exact (Subtype.ext hyx : y = x) ▸ hy
    · exact le_top
  have hσ : σ ∉ zpowers ρ := by
    intro hs
    apply hwU
    obtain ⟨k, hk⟩ := hs
    have hk' : r ^ k = w := congrArg Subtype.val hk
    rw [← hk']
    exact U.zpow_mem hrU k
  obtain ⟨e⟩ := dihedral_of_generators_of_not_mem ρ σ hgen
    (Subtype.ext hw2) (Subtype.ext (hinv r hrU)) hσ
  have ho : orderOf ρ = Nat.card U := by
    rw [Subgroup.orderOf_mk, ← Nat.card_zpowers, hr]
  change Nat.card D = _
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card, ho]

/-- An inner involution of PGL₂ over an odd prime field has centralizer
order dividing twice the appropriate p-1 or p+1. The even torus half
selects the appropriate sign. -/
theorem pgl_inner_centralizer_divisibility
    {K : Type*} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hK : Nat.card K = p)
    (z : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range)
    (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1) :
    (Even ((p - 1) / 2) ∧ Nat.card (centralizer ({(z : PGL2 K)} : Set (PGL2 K))) ∣
      2 * (p - 1)) ∨
    (Even ((p + 1) / 2) ∧ Nat.card (centralizer ({(z : PGL2 K)} : Set (PGL2 K))) ∣
      2 * (p + 1)) := by
  have hKodd : IsOddPrimePower (Nat.card K) := ⟨p, 1, hp, hodd, by decide, by simpa⟩
  let N := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range
  let e : PSL2 K ≃* N := psl2EquivToPGLRange K
  let t : PSL2 K := e.symm z
  have ht1 : t ≠ 1 := by
    intro h
    apply hz1
    simpa only [t, e.apply_symm_apply, map_one] using congrArg e h
  have ht2 : t ^ 2 = 1 := by
    dsimp [t]
    rw [← map_pow, hz2, map_one]
  obtain ⟨U, w, hU, _htU, hw, hwU, hinv, hC, heven, hcard⟩ :=
    psl2_reflected_torus_card hKodd ⟨ht1, ht2⟩
  have hc : Nat.card (centralizer ({z} : Set N)) = 2 * Nat.card U := by
    rw [← e.apply_symm_apply z, ← centralizer_card_equiv e, hC,
      reflected_join_card U hU w hwU hw.2 hinv]
  have hd := centralizer_card_dvd_index_two N (pgl2_psl2Range_index_eq_two K hKodd) z
  rw [hc] at hd
  have hminus : 2 * ((p - 1) / 2) = p - 1 := by obtain ⟨a, ha⟩ := hodd; omega
  have hplus : 2 * ((p + 1) / 2) = p + 1 := by obtain ⟨a, ha⟩ := hodd; omega
  rcases hcard with h | h
  · rw [h, hK] at heven hd
    exact Or.inl ⟨heven, by simpa only [hminus] using hd⟩
  · rw [h, hK] at heven hd
    exact Or.inr ⟨heven, by simpa only [hplus] using hd⟩

/-- Every four-group in the actual PGL₂(p) model contains an inner
involution to which the preceding divisibility calculation applies. -/
theorem pgl_actor_centralizer_divisibility
    {G K : Type*} [Group G] [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hodd : Odd p) (hK : Nat.card K = p)
    (A M : Subgroup G) (hA : IsKleinFour A) (hAM : A ≤ M)
    (eM : M ≃* PGL2 K) :
    ∃ z : G, z ∈ A ∧ z ≠ 1 ∧
      ((Even ((p - 1) / 2) ∧
          Nat.card ((centralizer ({z} : Set G)).subgroupOf M) ∣ 2 * (p - 1)) ∨
        (Even ((p + 1) / 2) ∧
          Nat.card ((centralizer ({z} : Set G)).subgroupOf M) ∣ 2 * (p + 1))) := by
  let N := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range
  let B := (A.subgroupOf M).map eM.toMonoidHom
  have hB : IsKleinFour B := isKleinFour_map_mulEquiv_cross _
    (isKleinFour_subgroupOf hAM hA) eM
  have hKodd : IsOddPrimePower (Nat.card K) := ⟨p, 1, hp, hodd, by decide, by simpa⟩
  obtain ⟨z, hzB, hzN, hz1⟩ := kleinFour_meets_index_two B N hB
    (pgl2_psl2Range_index_eq_two K hKodd)
  obtain ⟨a, ha, haz⟩ := hzB
  change eM a = z at haz
  have ha1 : (a : G) ≠ 1 := by
    intro h
    apply hz1
    rw [← haz, (Subtype.ext h : a = 1), map_one]
  have hz2 : z ^ 2 = 1 := by
    let : IsKleinFour B := hB
    rw [pow_two]
    exact congrArg Subtype.val (IsKleinFour.mul_self (⟨z, ⟨a, ha, haz⟩⟩ : B))
  have hdiv := pgl_inner_centralizer_divisibility hp hodd hK (⟨z, hzN⟩ : N)
    (fun h => hz1 (congrArg Subtype.val h)) (Subtype.ext hz2)
  refine ⟨a, ha, ha1, ?_⟩
  rw [relative_centralizer_card_equiv M eM a, haz]
  exact hdiv
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.InnerPlacement.CentralizerPrimes
