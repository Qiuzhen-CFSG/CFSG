module
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankProduct
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Theory.ElementaryAbelian.Quotient


/-!
# Prime rank of an exchanged cyclic pair

An index-two factor stabilizer has two cyclic coordinates whose kernels
are separated by every element exchanging the factors. Its two-rank is at
most two: elementary subgroups in the stabilizer embed in two cyclic groups,
while those meeting the other coset have cyclic intersection with it.
The statements descend through a common normal kernel and retain the
additive prime-rank bound across a subgroup of prescribed index.

Source application: Aschbacher--Smith, the double linear branch of 2.4.7,
printed p.540, on the actual two field-automorphism coordinates.
-/

public section

open Subgroup Theory.GroupTheory

namespace Theory.GroupTheory
variable {G C : Type*} [Group G] [Finite G] [Group C] [Finite C] [IsCyclic C]

private theorem cyclic_rank_le_one : primeRank 2 C ≤ 1 := by
  let P : Sylow 2 C := Classical.choice inferInstance
  exact P.primeRank_le_one_of_isCyclic inferInstance

/-- The cyclic coordinate kernels of a two-factor action are separated by
all elements which exchange the factors. -/
theorem primeRank_le_two_of_cyclic_pair
    (B : Subgroup G) [B.Normal] (hi : B.index = 2) (f : B →* C)
    (hsep : ∀ x : G, x ∉ B → ∀ b : B,
      f b = 1 → f (MulAut.conjNormal x b) = 1 → b = 1) :
    primeRank 2 G ≤ 2 := by
  classical
  have hout : ∃ x : G, x ∉ B := by
    by_contra hh
    have hb : B = ⊤ := top_unique (by intro y _; exact not_not.mp (fun hy => hh ⟨y,hy⟩))
    simp only [hb, index_top] at hi
    omega
  obtain ⟨x,hx⟩ := hout
  let F : B →* C × C := f.prod (f.comp (MulAut.conjNormal x).toMonoidHom)
  have hF : Function.Injective F := by
    apply (MonoidHom.ker_eq_bot_iff F).mp
    apply eq_bot_iff.mpr
    intro b hb
    change (f b, f (MulAut.conjNormal x b)) = (1,1) at hb
    exact hsep x hx b (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  have hB : primeRank 2 B ≤ 2 := by
    have h := primeRank_le_of_injective 2 F hF
    rw [primeRank_prod_eq_add] at h
    exact h.trans (by have := cyclic_rank_le_one (C := C); omega)
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro E hE
  let := hE
  by_cases hEB : E ≤ B
  · let e := subgroupOfEquivOfLe hEB
    have he : IsElementaryAbelian 2 (E.subgroupOf B) :=
      IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective
    have hc := (primeRank_le_iff_elementary_card_le B).mp hB (E.subgroupOf B) he
    rwa [Nat.card_congr e.toEquiv] at hc
  · obtain ⟨a,haE,haB⟩ := Set.not_subset.mp hEB
    let A := B.subgroupOf E
    let j : A →* C := f.comp
      { toFun := fun z => ⟨z.1.1,z.2⟩
        map_one' := rfl
        map_mul' _ _ := rfl }
    have hj : Function.Injective j := by
      apply j.ker_eq_bot_iff.mp
      apply eq_bot_iff.mpr
      intro b hb
      have hcomm : a * (b.1.1:G) = b.1.1 * a := by
        let : CommGroup E := IsMulCommutative.instCommGroup
        exact congrArg Subtype.val (mul_comm (⟨a,haE⟩:E) b.1)
      have he : MulAut.conjNormal a (⟨b.1.1,b.2⟩ : B) = ⟨b.1.1,b.2⟩ := by
        apply Subtype.ext
        change a * b.1.1 * a⁻¹ = b.1.1
        rw [hcomm,mul_inv_cancel_right]
      have hz := hsep a haB (⟨b.1.1,b.2⟩ : B) hb (by rw [he]; exact hb)
      exact Subtype.ext (Subtype.ext (congrArg (fun z : B => (z:G)) hz))
    have hA : primeRank 2 A ≤ 1 :=
      (primeRank_le_of_injective 2 j hj).trans (cyclic_rank_le_one (C := C))
    have hindex : A.index ≤ 2 ^ 1 := by
      change B.relIndex E ≤ 2 ^ 1
      calc B.relIndex E ≤ B.index := by
             simpa only [relIndex_top_right] using
               (relIndex_le_of_le_right (H := B) (K := E) (L := ⊤) le_top (by
                 simpa only [relIndex_top_right] using B.index_ne_zero_of_finite))
           _ = 2 ^ 1 := by rw [hi]; rfl
    have hr : primeRank 2 E ≤ 2 :=
      (primeRank_le_add_of_index_le A hindex).trans (by omega)
    have hh := (primeRank_le_iff_elementary_card_le E).mp hr (⊤ : Subgroup E)
      (IsElementaryAbelian.of_surjective
        (Subgroup.topEquiv : (⊤ : Subgroup E) ≃* E).symm.toMonoidHom
        (Subgroup.topEquiv : (⊤ : Subgroup E) ≃* E).symm.surjective)
    simpa only [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup E) ≃* E).toEquiv] using hh
end Theory.GroupTheory

namespace Theory.GroupTheory
variable {G C : Type*} [Group G] [Finite G] [Group C] [Finite C] [IsCyclic C]

/-- The preceding coordinate bound descends through its common kernel. -/
theorem primeRank_quotient_le_two_of_cyclic_pair
    (B N : Subgroup G) [B.Normal] [N.Normal]
    (hi : B.index = 2) (hNB : N ≤ B) (f : B →* C)
    (hNf : N.subgroupOf B ≤ f.ker)
    (hsep : ∀ x : G, x ∉ B → ∀ b : B,
      f b = 1 → f (MulAut.conjNormal x b) = 1 → (b:G) ∈ N) :
    primeRank 2 (G ⧸ N) ≤ 2 := by
  let q := QuotientGroup.mk' N
  let Bq := B.map q
  let qb : B →* Bq := q.subgroupMap B
  have hqb : (N.subgroupOf B) = qb.ker := by
    ext b
    change b.1 ∈ N ↔ qb b = 1
    rw [Subtype.ext_iff]
    exact (QuotientGroup.eq_one_iff (N := N) b.1).symm
  let e : (B ⧸ N.subgroupOf B) ≃* Bq :=
    QuotientGroup.liftEquiv (N.subgroupOf B) (q.subgroupMap_surjective B) hqb
  let fq : Bq →* C := (QuotientGroup.lift (N.subgroupOf B) f hNf).comp e.symm.toMonoidHom
  have hcalc (b : B) : fq (qb b) = f b := by
    have he : e (QuotientGroup.mk' (N.subgroupOf B) b) = qb b :=
      QuotientGroup.liftEquiv_mk (N.subgroupOf B) (q.subgroupMap_surjective B) hqb b
    rw [←he]
    change QuotientGroup.lift (N.subgroupOf B) f hNf
      (e.symm (e (QuotientGroup.mk' (N.subgroupOf B) b))) = f b
    rw [e.symm_apply_apply]
    rfl
  have hBq : Bq.index = 2 := by
    rw [show Bq = B.map q from rfl, B.index_map_eq (QuotientGroup.mk'_surjective N) (by
      rw [QuotientGroup.ker_mk']
      exact hNB),hi]
  apply primeRank_le_two_of_cyclic_pair Bq hBq fq
  intro x hx b hb hbc
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective N x
  have hy : y ∉ B := fun hy => hx (mem_map_of_mem q hy)
  obtain ⟨a,rfl⟩ := q.subgroupMap_surjective B b
  have hconj : MulAut.conjNormal (q y) (qb a) = qb (MulAut.conjNormal y a) := by
    apply Subtype.ext
    change q y * q a.1 * (q y)⁻¹ = q (y * a.1 * y⁻¹)
    simp only [map_mul,map_inv]
  rw [hconj,hcalc] at hbc
  rw [hcalc] at hb
  apply Subtype.ext
  exact (QuotientGroup.eq_one_iff a.1).mpr (hsep y hy a hb hbc)
end Theory.GroupTheory

namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The quotient by a subgroup inside a small-index subgroup inherits the
same additive prime-rank estimate. -/
theorem primeRank_quotient_le_add_of_index_le
    {p k n : ℕ} [Fact p.Prime] (N B : Subgroup G) [N.Normal]
    (hNB : N ≤ B) (hi : B.index ≤ p^n)
    (hr : primeRank p (B ⧸ N.subgroupOf B) ≤ k) :
    primeRank p (G ⧸ N) ≤ k+n := by
  let q := QuotientGroup.mk' N
  let Bq := B.map q
  let qb : B →* Bq := q.subgroupMap B
  have hqb : (N.subgroupOf B) = qb.ker := by
    ext b
    change b.1 ∈ N ↔ qb b = 1
    rw [Subtype.ext_iff]
    exact (QuotientGroup.eq_one_iff (N := N) b.1).symm
  let e : (B ⧸ N.subgroupOf B) ≃* Bq :=
    QuotientGroup.liftEquiv (N.subgroupOf B) (q.subgroupMap_surjective B) hqb
  have hBq : Bq.index ≤ p^n := by
    rw [show Bq = B.map q from rfl, B.index_map_eq (QuotientGroup.mk'_surjective N) (by
      rw [QuotientGroup.ker_mk']; exact hNB)]
    exact hi
  have hr' : primeRank p Bq ≤ k := by rwa [←primeRank_equiv p e]
  exact (primeRank_le_add_of_index_le Bq hBq).trans (Nat.add_le_add_right hr' n)
end Theory.GroupTheory
