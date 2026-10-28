module
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupAction.SubgroupConjugation
/-!
# Odd-prime rank from two commuting conjugate planes

Let B contain a noncentral elementary subgroup E of order p². If B commutes
with its conjugate, choose an order-p element of E outside Z(B). Its cyclic
subgroup is disjoint from the conjugate plane: a common nonidentity element
would centralize B, forcing the chosen cyclic subgroup into Z(B). Their
commuting join therefore has prime rank at least three.

This is the rank contradiction used in Aschbacher--Smith A.3.8(3), p.46.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem Subgroup.three_le_primeRank_of_commuting_conjugate_plane
    (B : Subgroup G) (g : G) (hcomm : B ≤ centralizer (B.conjBy g : Set G))
    (E : Subgroup B) [IsElementaryAbelian p E] (hE : Nat.card E = p ^ 2)
    (hn : ¬ E ≤ center B) : 3 ≤ primeRank p G := by
  obtain ⟨x,hx,hxz⟩ := Set.not_subset.mp hn
  have hxp : x ^ p = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p E) ⟨x,hx⟩)
  have hx1 : x ≠ 1 := by
    intro he
    exact hxz (he ▸ (center B).one_mem)
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hd := (center B).disjoint_zpowers_of_prime_order_not_mem x hxo hxz
  let C := (zpowers x).map B.subtype
  let D := (E.map B.subtype).conjBy g
  have hCB : C ≤ B := map_subtype_le _
  have hDB : D ≤ B.conjBy g := map_mono (map_subtype_le E)
  have hCD : C ≤ centralizer (D : Set G) :=
    hCB.trans (hcomm.trans (centralizer_le hDB))
  have hdis : Disjoint C D := by
    apply disjoint_def.mpr
    rintro _ ⟨y,hy,rfl⟩ hz
    have hyc : y ∈ center B := by
      apply mem_center_iff.mpr
      intro b
      exact Subtype.ext (hcomm b.property y (hDB hz)).symm
    exact congrArg Subtype.val (disjoint_def.mp hd hyc hy)
  have hc : Nat.card C = p := by
    rw [card_map_of_injective B.subtype_injective, Nat.card_zpowers, hxo]
  have hc1 : 1 ≤ primeRank p C := by
    let : CommGroup C := IsMulCommutative.instCommGroup
    exact primeRank_ge_of_elementary_embedding
      (fun c => hc ▸ pow_card_eq_one' (x := c)) (by simpa using hc)
      (MonoidHom.id C) Function.injective_id
  let : IsElementaryAbelian p (E.map B.subtype) := IsElementaryAbelian.map _
  let : IsElementaryAbelian p D := IsElementaryAbelian.map _
  have hdcard : Nat.card D = p ^ 2 := by
    change Nat.card ((E.map B.subtype).map (MulAut.conj g).toMonoidHom) = p ^ 2
    rw [card_map_of_injective (MulAut.conj g).injective,
      card_map_of_injective B.subtype_injective,hE]
  have hd2 : 2 ≤ primeRank p D := by
    let : CommGroup D := IsMulCommutative.instCommGroup
    exact primeRank_ge_of_elementary_embedding
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p D))
      hdcard (MonoidHom.id D) Function.injective_id
  have he := C.primeRank_sup_eq_add_of_disjoint_commuting D hdis hCD p
  have hle := Theory.GroupTheory.primeRank_le_of_injective p (C ⊔ D).subtype (C ⊔ D).subtype_injective
  omega
