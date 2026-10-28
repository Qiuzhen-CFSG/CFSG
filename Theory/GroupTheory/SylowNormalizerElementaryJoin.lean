module
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.PCoreAbelianQuotient
public import Theory.GroupTheory.PCoreRestriction
public import Theory.ElementaryAbelian.Quotient
/-!
# Characteristic Sylow overgroups from full elementary rank

If the normalizer of a Sylow two-subgroup has abelian quotient by that
Sylow, a permuting elementary p-subgroup of the full ambient p-rank
fills the first omega subgroup of the quotient. Its join with the Sylow
is therefore characteristic in the Sylow normalizer. In particular every
automorphism preserving the Sylow preserves this join.

This is the characteristic-subgroup step for the binary rank-one branch
of Aschbacher--Smith 10.2.5, printed p.748. The rank and elementary
hypotheses are essential: an arbitrary odd subgroup need not be preserved.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
private theorem characteristic_of_elementary_full_rank {p n : ℕ} [Fact p.Prime]
    [IsMulCommutative G] (E : Subgroup G) [IsElementaryAbelian p E]
    (hr : primeRank p G ≤ n) (hc : Nat.card E = p ^ n) : E.Characteristic := by
  have he : E = omega₁ G (p := p) := by
    apply eq_of_le_of_card_ge elementaryAbelian_le_omega₁
    rw [hc]
    exact (primeRank_le_iff_elementary_card_le G).mp hr _
      (IsElementaryAbelian.omega₁_of_isMulCommutative G)
  rw [he]
  exact omega₁_characteristic G

omit [Finite G] in
private theorem core_sylow_normalizer (S : Sylow 2 G) :
    (normalizer (S : Set G)).pCoreIn 2 = (S : Subgroup G) := by
  apply le_antisymm
  · have hh := pCoreIn_le_sylow (normalizer (S : Set G))
      (S.subtype (S : Subgroup G).le_normalizer)
    rw [Sylow.coe_subtype] at hh
    change (normalizer (S : Set G)).pCoreIn 2 ≤
      ((S : Subgroup G).subgroupOf (normalizer (S : Set G))).map
        (normalizer (S : Set G)).subtype at hh
    rw [map_subgroupOf_eq_of_le (show (S : Subgroup G) ≤ normalizer (S : Set G) from
      (S : Subgroup G).le_normalizer)] at hh
    exact hh
  · exact le_pCoreIn_of_normalizes S.isPGroup' (S : Subgroup G).le_normalizer le_rfl

/-- The elementary subgroup fills first omega in the abelian Sylow quotient. -/
theorem sylow_join_characteristic_of_elementary (S : Sylow 2 G) (P : Subgroup G)
    {p n : ℕ} [Fact p.Prime] (hp : Odd p) [IsElementaryAbelian p P]
    (hP : Nat.card P = p ^ n) (hr : primeRank p G ≤ n)
    (hPN : P ≤ normalizer (S : Set G))
    (hd : ⁅normalizer (S : Set G),normalizer (S : Set G)⁆ ≤ (S : Subgroup G)) :
    ((P ⊔ (S : Subgroup G)).subgroupOf (normalizer (S : Set G))).Characteristic := by
  let N := normalizer (S : Set G)
  let B := (P ⊔ (S : Subgroup G)).subgroupOf N
  let A := P.subgroupOf N
  let q := QuotientGroup.mk' (pCore 2 N)
  have hc : N.pCoreIn 2 = (S : Subgroup G) := core_sylow_normalizer S
  have hcore : pCore 2 N ≤ B := by
    intro x hx
    exact mem_sup_right (hc ▸ mem_map_of_mem N.subtype hx)
  let : IsMulCommutative (N ⧸ pCore 2 N) :=
    (commutator_self_le_pCoreIn_iff 2 N).mp (hc.symm ▸ hd)
  have hpA : IsElementaryAbelian p A :=
    IsElementaryAbelian.of_surjective (subgroupOfEquivOfLe hPN).symm.toMonoidHom
      (subgroupOfEquivOfLe hPN).symm.surjective
  let := hpA
  have hi : Function.Injective (q.subgroupMap A) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hxq : q x.val = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hxS : (x.val : G) ∈ (S : Subgroup G) :=
      hc ▸ mem_map_of_mem N.subtype ((QuotientGroup.eq_one_iff x.val).mp hxq)
    have hdis := (IsElementaryAbelian.isPGroup p P).disjoint_of_coprime S.isPGroup'
      hp.coprime_two_right
    exact Subtype.ext (Subtype.ext (hdis.le_bot ⟨x.property,hxS⟩))
  have hB : B.map q = A.map q := by
    rw [show B = A ⊔ (S : Subgroup G).subgroupOf N from
      subgroupOf_sup hPN (S : Subgroup G).le_normalizer,Subgroup.map_sup]
    have hs : (S : Subgroup G).subgroupOf N = pCore 2 N := by
      apply map_injective N.subtype_injective
      rw [map_subgroupOf_eq_of_le (show (S : Subgroup G) ≤ N from (S : Subgroup G).le_normalizer)]
      exact hc.symm
    rw [hs,QuotientGroup.map_mk'_self,sup_bot_eq]
  let : IsElementaryAbelian p (B.map q) := by
    rw [hB]
    exact IsElementaryAbelian.of_surjective (q.subgroupMap A) (q.subgroupMap_surjective A)
  have hcard : Nat.card (B.map q) = p ^ n := by
    rw [hB,← Nat.card_congr (Equiv.ofBijective (q.subgroupMap A)
      ⟨hi,q.subgroupMap_surjective A⟩),Nat.card_congr (subgroupOfEquivOfLe hPN).toEquiv]
    exact hP
  have hrq : primeRank p (N ⧸ pCore 2 N) ≤ n :=
    (primeRank_quotient_le_of_isTwoGroup p hp _ pCore_isPGroup).trans
      ((primeRank_subgroup_le p N).trans hr)
  have hchar := characteristic_of_elementary_full_rank (B.map q) hrq hcard
  have hh := Characteristic.comap_quotient_mk hchar
  change ((B.map q).comap q).Characteristic at hh
  rw [comap_map_eq,QuotientGroup.ker_mk',sup_of_le_left hcore] at hh
  exact hh

/-- Every automorphism preserving the same Sylow preserves its elementary join. -/
theorem map_sylow_join_of_elementary (S : Sylow 2 G) (P : Subgroup G)
    {p n : ℕ} [Fact p.Prime] (hp : Odd p) [IsElementaryAbelian p P]
    (hP : Nat.card P = p ^ n) (hr : primeRank p G ≤ n)
    (hPN : P ≤ normalizer (S : Set G))
    (hd : ⁅normalizer (S : Set G),normalizer (S : Set G)⁆ ≤ (S : Subgroup G))
    (a : MulAut G) (ha : (S : Subgroup G).map a.toMonoidHom = S) :
    (P ⊔ (S : Subgroup G)).map a.toMonoidHom = P ⊔ S := by
  let N := normalizer (S : Set G)
  have hN : N.map a.toMonoidHom = N := by
    change (normalizer ((S : Subgroup G) : Set G)).map a.toMonoidHom =
      normalizer ((S : Subgroup G) : Set G)
    rw [map_equiv_normalizer_eq,ha]
  let b : MulAut N := (a.subgroupMap N).trans (MulEquiv.subgroupCongr hN)
  let B := (P ⊔ (S : Subgroup G)).subgroupOf N
  let : B.Characteristic := sylow_join_characteristic_of_elementary S P hp hP hr hPN hd
  have hb := characteristic_iff_map_eq.mp (inferInstance : B.Characteristic) b
  have he := congrArg (Subgroup.map N.subtype) hb
  rw [Subgroup.map_map] at he
  have hnatur : N.subtype.comp b.toMonoidHom = a.toMonoidHom.comp N.subtype := rfl
  rw [hnatur,← Subgroup.map_map,map_subgroupOf_eq_of_le
    (sup_le hPN (S : Subgroup G).le_normalizer)] at he
  exact he
end Subgroup
