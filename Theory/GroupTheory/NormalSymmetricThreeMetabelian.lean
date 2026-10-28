module

public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Solvable

/-!
# Second derived groups above a normal symmetric-three section

A normal S₃ splits off its centralizer because its center and outer
automorphism group are trivial. Consequently a group of order 36 with a
normal S₃ is metabelian. If a normal subgroup N has index six and
N/O₂(N) is S₃, this applies after quotienting by the embedded O₂(N):
the ambient second derived subgroup is a two-group.

The actual binary extended unitary-four point stabilizer supplies N as
its ordinary vector stabilizer. This is the endpoint invariant used in
Aschbacher–Smith F.4.36, printed p.292.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
open NormalSymmetricThreePairRank
variable {G : Type*} [Group G] [Finite G]

/-- Groups of order six have trivial second derived subgroup. -/
theorem derivedTwo_eq_bot_of_card_six (hG : Nat.card G = 6) :
    derivedSeries G 2 = ⊥ := by
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 (by rw [hG]; decide)
  let A := zpowers a
  have hA : Nat.card A = 3 := (Nat.card_zpowers a).trans ha
  have hi : A.index = 2 := by
    have hc := A.card_mul_index
    rw [hA,hG] at hc
    omega
  let : A.Normal := normal_of_index_eq_two hi
  let : IsCyclic (G ⧸ A) := isCyclic_of_prime_card (p := 2)
    (by change A.index = 2; exact hi)
  let : IsCyclic A := isCyclic_of_prime_card hA
  have hd : derivedSeries G 1 ≤ A := by
    have hh := map_derivedSeries_le_derivedSeries (QuotientGroup.mk' A) 1
    rw [derivedSeries_one (G ⧸ A), commutator_eq_bot] at hh
    simpa only [Subgroup.map_le_iff_le_comap, MonoidHom.comap_bot,
      QuotientGroup.ker_mk'] using hh
  apply le_antisymm _ bot_le
  exact (commutator_mono hd hd).trans
    (commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative A)).le

omit [Finite G] in
private theorem normal_symmetricThree_split (H : Subgroup G) [H.Normal]
    (j : H ≃* Equiv.Perm (Fin 3)) :
    Nonempty (H × centralizer (H : Set G) ≃* G) := by
  let C := centralizer (H : Set G)
  have hd : Disjoint H C := by
    apply disjoint_def.mpr
    intro x hx hc
    have hz : j ⟨x,hx⟩ = 1 := by
      apply symmetricThree_center_trivial
      intro y
      have he : j.symm y * (⟨x,hx⟩ : H) = ⟨x,hx⟩ * j.symm y :=
        Subtype.ext (mem_centralizer_iff.mp hc _ (j.symm y).property)
      simpa only [map_mul,j.apply_symm_apply] using congrArg j he
    exact congrArg Subtype.val (j.injective (hz.trans j.map_one.symm))
  have hs : H ⊔ C = ⊤ := by
    apply top_unique
    intro g _
    let α : MulAut (Equiv.Perm (Fin 3)) := j.symm.trans ((MulAut.conjNormal g).trans j)
    obtain ⟨k,hk⟩ := symmetricThree_aut_inner α
    let h : H := j.symm k
    have he (x : H) : g * (x : G) * g⁻¹ = (h * x * h⁻¹ : H) := by
      change ((MulAut.conjNormal g x : H) : G) = _
      apply congrArg (fun a : H => (a : G))
      apply j.injective
      have hh := DFunLike.congr_fun hk (j x)
      simpa [α,h,MulAut.conj_apply] using hh
    have hc : (h : G)⁻¹ * g ∈ C := by
      apply mem_centralizer_iff.mpr
      intro x hx
      have hh := congrArg (fun a : G => (h : G)⁻¹ * a * g) (he ⟨x,hx⟩)
      simpa [mul_assoc] using hh.symm
    have hm := (H ⊔ C).mul_mem
      ((show H ≤ H ⊔ C from le_sup_left) h.property)
      ((show C ≤ H ⊔ C from le_sup_right) hc)
    simpa only [← mul_assoc,mul_inv_cancel,one_mul] using hm
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting H C hd
    (le_centralizer_iff.mpr le_rfl)
  exact ⟨e.trans ((MulEquiv.subgroupCongr hs).trans topEquiv)⟩

/-- A normal symmetric-three subgroup in order 36 forces derived length at most two. -/
theorem derivedTwo_eq_bot_of_normal_symmetricThree
    (hG : Nat.card G = 36) (H : Subgroup G) [H.Normal]
    (j : H ≃* Equiv.Perm (Fin 3)) : derivedSeries G 2 = ⊥ := by
  obtain ⟨e⟩ := normal_symmetricThree_split H j
  let C := centralizer (H : Set G)
  have hH : Nat.card H = 6 := by
    rw [Nat.card_congr j.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  have hC : Nat.card C = 6 := by
    have hc := Nat.card_congr e.toEquiv
    rw [Nat.card_prod,hH,hG] at hc
    change 6 * Nat.card C = 36 at hc
    omega
  have hp : derivedSeries (H × C) 2 = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have h₁ := map_derivedSeries_le_derivedSeries (MonoidHom.fst H C) 2
      (mem_map_of_mem _ hx)
    have h₂ := map_derivedSeries_le_derivedSeries (MonoidHom.snd H C) 2
      (mem_map_of_mem _ hx)
    rw [derivedTwo_eq_bot_of_card_six hH] at h₁
    rw [derivedTwo_eq_bot_of_card_six hC] at h₂
    exact Prod.ext h₁ h₂
  rw [← map_derivedSeries_eq (f := e.toMonoidHom) e.surjective 2, hp, Subgroup.map_bot]

/-- The second derived group is a two-group when a normal index-six subgroup
has its actual two-core quotient isomorphic to S₃. -/
theorem derivedTwo_isTwoGroup_of_normal_indexSix
    (N : Subgroup G) [N.Normal] (hindex : N.index = 6)
    (j : (N ⧸ pCore 2 N) ≃* Equiv.Perm (Fin 3)) :
    IsPGroup 2 (derivedSeries G 2) := by
  let K := (pCore 2 N).map N.subtype
  have hKN : K ≤ N := map_subtype_le _
  let : K.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    have h := normalizer_le_normalizer_characteristic_image N (pCore 2 N)
    rwa [N.normalizer_eq_top] at h
  let q := QuotientGroup.mk' K
  let H := N.map q
  let f : N →* G ⧸ K := q.comp N.subtype
  have hker : f.ker = pCore 2 N := by
    have he : f.ker = K.comap N.subtype := by
      ext x
      exact QuotientGroup.eq_one_iff (x : G)
    rw [he]
    exact comap_map_eq_self_of_injective N.subtype_injective _
  have hrange : f.range = H := by rw [MonoidHom.range_comp, range_subtype]
  let e : H ≃* Equiv.Perm (Fin 3) :=
    ((MulEquiv.subgroupCongr hrange.symm).trans
      (QuotientGroup.quotientKerEquivRange f).symm).trans
        ((QuotientGroup.quotientMulEquivOfEq hker).trans j)
  have hcard : Nat.card (G ⧸ K) = 36 := by
    change K.index = 36
    rw [index_map_subtype, hindex, index_eq_card,
      Nat.card_congr j.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  have hd := derivedTwo_eq_bot_of_normal_symmetricThree hcard H e
  have hle : derivedSeries G 2 ≤ K := by
    have hh := map_derivedSeries_le_derivedSeries q 2
    rw [hd] at hh
    simpa only [map_le_iff_le_comap, MonoidHom.comap_bot, q, QuotientGroup.ker_mk'] using hh
  exact ((pCore_isPGroup (p := 2) (G := N)).map N.subtype).to_le hle

end Theory.GroupTheory
