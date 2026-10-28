module

public import Theory.GroupTheory.Hall.Conjugacy
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# Hall control above a normal subgroup with abelian two-core quotient

Suppose N is normal in a finite group G, G/N is a two-group, and
N/O₂(N) is abelian. Then G is solvable and every odd Hall subgroup Y
is abelian. For each Sylow two-subgroup S, the normal subgroup
Q = O₂(N), embedded in G, satisfies S = Q N_S(Y).

The abelian quotient makes O₂(N) Sylow in N. Hall arithmetic gives
N = QY, and Hall conjugacy in N adjusts every conjugation by S by an
element of Q. Thus the normalizer factorization uses the original S.

Source: the Borel and Frattini arguments in Aschbacher--Smith, 4.4.13,
printed pp.623--624. Only finite solvable Hall theory is used here.
-/

@[expose] public section

open Subgroup
open scoped Pointwise IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem oddHall_complement_sylow (Y : Subgroup G)
    (hY : IsHallSubgroup {q : Nat.Primes | q.val ≠ 2} Y) (S : Sylow 2 G) :
    (S : Subgroup G).IsComplement' Y := by
  have hYtwo : ¬ 2 ∣ Nat.card Y := fun h =>
    hY.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ h rfl
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
  have hcop_cards : Nat.Coprime (Nat.card Y) (Nat.card S) := by
    rw [hn]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr hYtwo).symm.pow_right n
  have hcop_indices : Nat.Coprime (S : Subgroup G).index Y.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpS hpY
    have hp2 : p = 2 := Classical.not_not.mp
      (hY.p_in_pi_of_p_dvd_index ⟨p, hp⟩ hpY)
    exact S.not_dvd_index (hp2 ▸ hpS)
  have hcard_dvd_index : Nat.card Y ∣ (S : Subgroup G).index := by
    have hdvd : Nat.card Y ∣ (S : Subgroup G).index * Nat.card S := by
      simpa only [index_mul_card] using card_subgroup_dvd_card Y
    exact hcop_cards.dvd_of_dvd_mul_right hdvd
  have hindex_dvd_card : (S : Subgroup G).index ∣ Nat.card Y := by
    have hdvd : (S : Subgroup G).index ∣ Nat.card Y * Y.index := by
      simpa only [card_mul_index] using (S : Subgroup G).index_dvd_card
    exact hcop_indices.dvd_of_dvd_mul_right hdvd
  have hcardY : Nat.card Y = (S : Subgroup G).index :=
    Nat.dvd_antisymm hcard_dvd_index hindex_dvd_card
  refine isComplement'_of_coprime ?_ hcop_cards.symm
  rw [hcardY]
  exact (S : Subgroup G).card_mul_index

omit [Finite G] in
theorem sylow_eq_core_of_commutative_quotient {p : ℕ} [Fact p.Prime]
    [IsMulCommutative (G ⧸ pCore p G)] (S : Sylow p G) :
    (S : Subgroup G) = pCore p G := by
  let q := QuotientGroup.mk' (pCore p G)
  let C := (S : Subgroup G).map q
  have hpre : IsPGroup p (C.comap q) := (S.isPGroup'.map q).comap_of_ker_isPGroup q
    (by change IsPGroup p (QuotientGroup.mk' (pCore p G)).ker
        rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  exact le_antisymm ((le_comap_map q _).trans (le_sSup ⟨inferInstance, hpre⟩))
    (pCore_isPGroup.le_sylow_of_normal S)

theorem solvable_of_commutative_core_quotient [IsMulCommutative (G ⧸ pCore 2 G)] :
    Group.IsSolvable G := by
  let : Group.IsNilpotent (pCore 2 G) := (pCore_isPGroup (p := 2) (G := G)).isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 G)).mpr ⟨inferInstance, inferInstance⟩

omit [Finite G] in
theorem hall_le_normal_of_two_quotient (N Y : Subgroup G) [N.Normal]
    (hN : IsPGroup 2 (G ⧸ N)) (hY : IsHallSubgroup {q : Nat.Primes | q.val ≠ 2} Y) : Y ≤ N := by
  have hnot : ¬ 2 ∣ Nat.card Y := fun h =>
    hY.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ h rfl
  intro y hy
  apply (show pResidual 2 G ≤ N from sInf_le ⟨inferInstance, hN⟩)
  apply mem_pResidual_of_orderOf_coprime
  apply (Nat.prime_two.coprime_iff_not_dvd.mpr hnot).of_dvd_right
  simpa only [Subgroup.orderOf_mk] using _root_.orderOf_dvd_natCard (⟨y, hy⟩ : Y)

theorem hall_control_from_normal_core_quotient (N : Subgroup G) [N.Normal]
    (hN : IsPGroup 2 (G ⧸ N)) [IsMulCommutative (N ⧸ pCore 2 N)]
    (S : Sylow 2 G) :
    Group.IsSolvable G ∧ ∀ Y : Subgroup G, IsHallSubgroup {q : Nat.Primes | q.val ≠ 2} Y →
      IsMulCommutative Y ∧ ∃ Q : Subgroup G, Y ≤ normalizer (Q : Set G) ∧
        (S : Set G) = (Q : Set G) *
          ((S : Subgroup G) ⊓ normalizer (Y : Set G) : Set G) := by
  let : Group.IsSolvable N := solvable_of_commutative_core_quotient
  let : Group.IsNilpotent (G ⧸ N) := hN.isNilpotent
  have hsolv : Group.IsSolvable G := (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, inferInstance⟩
  refine ⟨hsolv, ?_⟩
  intro Y hY
  have hYN := hall_le_normal_of_two_quotient N Y hN hY
  let YN := Y.subgroupOf N
  have hYNhall : IsHallSubgroup {q : Nat.Primes | q.val ≠ 2} YN := hY.subgroupOf hYN
  let P : Sylow 2 N := Classical.choice inferInstance
  have hP : (P : Subgroup N) = pCore 2 N := sylow_eq_core_of_commutative_quotient P
  have hcomp : (pCore 2 N).IsComplement' YN := hP ▸ oddHall_complement_sylow YN hYNhall P
  let Q := (pCore 2 N).map N.subtype
  have hQnormal : Q.Normal := inferInstance
  have hQtwo : IsPGroup 2 Q := pCore_isPGroup.map N.subtype
  have hQS : Q ≤ S := hQtwo.le_sylow_of_normal S
  have hYNcomm : IsMulCommutative YN := by
    let q := (QuotientGroup.mk' (pCore 2 N)).comp YN.subtype
    have hqi : Function.Injective q := by
      apply (MonoidHom.ker_eq_bot_iff q).mp
      apply eq_bot_iff.mpr
      intro y hy
      have hyQ : y.val ∈ pCore 2 N := (QuotientGroup.eq_one_iff _).mp (show q y = 1 from hy)
      apply Subtype.ext
      exact Subgroup.disjoint_def.mp hcomp.disjoint hyQ y.property
    refine ⟨⟨fun x y => hqi ?_⟩⟩
    simp only [map_mul]
    exact (inferInstance : IsMulCommutative (N ⧸ pCore 2 N)).is_comm.comm _ _
  have hYcomm : IsMulCommutative Y := by
    let e := (subgroupOfEquivOfLe hYN).symm
    refine ⟨⟨fun x y => e.injective ?_⟩⟩
    simp only [map_mul]
    exact hYNcomm.is_comm.comm _ _
  refine ⟨hYcomm, Q, le_normalizer_of_normal, ?_⟩
  apply Set.Subset.antisymm
  · intro s hs
    let Y' := Y.map (MulAut.conj s).toMonoidHom
    have hY'N : Y' ≤ N := by
      rintro _ ⟨y, hy, rfl⟩
      exact (inferInstance : N.Normal).conj_mem y (hYN hy) s
    have hY'hall : IsHallSubgroup {q : Nat.Primes | q.val ≠ 2} (Y'.subgroupOf N) :=
      (hY.map_conj s).subgroupOf hY'N
    obtain ⟨n, hn⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable
      (inferInstance : Group.IsSolvable N) hYNhall hY'hall
    have hnG : Y' = Y.map (MulAut.conj (n : G)).toMonoidHom := by
      have he := congrArg (fun H : Subgroup N => H.map N.subtype) hn
      rw [map_subgroupOf_eq_of_le hY'N, map_map] at he
      rw [← map_subgroupOf_eq_of_le hYN, map_map]
      exact he
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp (hcomp.mul_eq ▸ Set.mem_univ n)
    have hbY : (b : G) ∈ Y := hb
    have hbnorm : Y.map (MulAut.conj (b : G)).toMonoidHom = Y :=
      mem_normalizer_iff_map_conj_eq.mp (Y.le_normalizer hbY)
    have hnab : (n : G) = (a : G) * (b : G) := (congrArg Subtype.val hab).symm
    have hna : Y.map (MulAut.conj (n : G)).toMonoidHom =
        Y.map (MulAut.conj (a : G)).toMonoidHom := by
      calc
        _ = (Y.map (MulAut.conj (b : G)).toMonoidHom).map
            (MulAut.conj (a : G)).toMonoidHom := by
          rw [map_map, hnab]
          congr 1
          ext x
          simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
            MulAut.conj_apply]
          group
        _ = _ := by rw [hbnorm]
    have haQ : (a : G) ∈ Q := mem_map_of_mem N.subtype ha
    let t := (a : G)⁻¹ * s
    have htS : t ∈ S := S.mul_mem (S.inv_mem (hQS haQ)) hs
    have htY : t ∈ normalizer (Y : Set G) := by
      rw [mem_normalizer_iff_map_conj_eq]
      apply (map_injective (f := (MulAut.conj (a : G)).toMonoidHom)
        (MulAut.conj (a : G)).injective)
      rw [map_map]
      have ht : (MulAut.conj (a : G)).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
          (MulAut.conj s).toMonoidHom := by
        ext x
        simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
          MulAut.conj_apply]
        dsimp only [t]
        group
      change Y.map ((MulAut.conj (a : G)).toMonoidHom.comp
        (MulAut.conj t).toMonoidHom) = Y.map (MulAut.conj (a : G)).toMonoidHom
      rw [ht]
      exact hnG.trans hna
    exact ⟨a, haQ, t, ⟨htS, htY⟩, mul_inv_cancel_left _ _⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact S.mul_mem (hQS ha) hb.1

end Subgroup
