module

public import Theory.GroupTheory.Recognition.DihedralEightCentralizer.LinearModel
public import Theory.SpecificGroups.PSL2.EvenOrder
public import Theory.SpecificGroups.PSL2.CubicNormalizerCongruence
public import GorensteinWalter.PGL2InnerAction
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# Restricting the field in the projective general linear case

The actual normal PSL2 range in PGL2 contains the marked central involution.
Involution fusion gives its product with the marked Sylow as the whole group.
Its index two therefore restricts the Sylow intersection to order four.
This intersection is exactly the involution centralizer inside PSL2.
The exact q−1 or q+1 centralizer formula forces q=3 or q=5.
-/

open Subgroup GorensteinWalter
noncomputable section
namespace Theory.GroupTheory.DihedralEightCentralizer
universe u

private theorem centralizer_card_four_of_index_two_psl2
    {H : Type u} [Group H] [Finite H]
    (S : Sylow 2 H) (eS : S ≃* DihedralGroup 4)
    (t : H) (ht : orderOf t = 2) (hC : centralizer ({t} : Set H) = S)
    (F : Type u) [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (N : Subgroup H) [N.Normal] (eN : N ≃* PSL2 F) (hi : N.index = 2) :
    ∃ htN : t ∈ N,
      Nat.card (centralizer ({(⟨t, htN⟩ : N)} : Set N)) = 4 := by
  have hNtwo : 2 ∣ Nat.card N := by
    rw [Nat.card_congr eN.toEquiv]
    exact Theory.PSL2.two_dvd_card
  have htN := involution_mem_normal S eS t ht hC N hNtwo
  have hsup := psl2_core_sup_eq_top S eS t ht hC F hF N eN
  have hrel : (N.subgroupOf (S : Subgroup H)).index = 2 := by
    change N.relIndex (S : Subgroup H) = 2
    rw [← Subgroup.relIndex_sup_right, hsup, Subgroup.relIndex_top_right, hi]
  have hScard : Nat.card S = 8 :=
    (Nat.card_congr eS.toEquiv).trans DihedralGroup.nat_card
  have hBcard : Nat.card (N.subgroupOf (S : Subgroup H)) = 4 := by
    have hh := (N.subgroupOf (S : Subgroup H)).index_mul_card
    rw [hrel, hScard] at hh
    omega
  let tN : N := ⟨t, htN⟩
  let e : (N.subgroupOf (S : Subgroup H)) ≃* centralizer ({tN} : Set N) := {
    toFun x := ⟨⟨x.val.val, x.property⟩, by
      apply mem_centralizer_singleton_iff.mpr
      apply Subtype.ext
      apply mem_centralizer_singleton_iff.mp
      rw [hC]
      exact x.val.property⟩
    invFun x := ⟨⟨x.val.val, by
      rw [← hC]
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩,
      x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  exact ⟨htN, (Nat.card_congr e.toEquiv).symm.trans hBcard⟩

/-- A PGL2 model of the marked dihedral-centralizer configuration has field
order three or five. This uses the full centralizer, not just Sylow order. -/
public theorem field_card_of_pgl2_model
    {H : Type u} [Group H] [Finite H]
    (S : Sylow 2 H) (eS : S ≃* DihedralGroup 4)
    (t : H) (ht : orderOf t = 2) (hC : centralizer ({t} : Set H) = S)
    {F : Type u} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (eH : H ≃* PGL2 F) :
    Nat.card F = 3 ∨ Nat.card F = 5 := by
  let J := (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
  have hJi : J.index = 2 := pgl2_psl2Range_index_eq_two F hF
  let : J.Normal := J.normal_of_index_eq_two hJi
  let N := J.comap eH.toMonoidHom
  let eNJ : N ≃* J := MulEquiv.ofBijective (eH.toMonoidHom.subgroupComap J)
    ⟨fun _ _ hh => Subtype.ext (eH.injective (congrArg Subtype.val hh)),
      eH.toMonoidHom.subgroupComap_surjective_of_surjective J eH.surjective⟩
  let eN : N ≃* PSL2 F := eNJ.trans (psl2EquivToPGLRange F).symm
  have hNi : N.index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ eH.surjective]
    exact hJi
  obtain ⟨htN, hc⟩ := centralizer_card_four_of_index_two_psl2
    S eS t ht hC F hF N eN hNi
  let tN : N := ⟨t, htN⟩
  have htI : IsInvolution (eN tN) := by
    constructor
    · intro he
      have he' : tN = 1 := eN.injective (he.trans (map_one eN).symm)
      have he'' : t = 1 := congrArg Subtype.val he'
      simp [he''] at ht
    · have hh : tN ^ 2 = 1 := Subtype.ext (ht ▸ pow_orderOf_eq_one t)
      simpa only [map_pow, map_one] using congrArg eN hh
  have hmap : (centralizer ({tN} : Set N)).map eN.toMonoidHom =
      centralizer ({eN tN} : Set (PSL2 F)) := by
    rw [map_centralizer_equiv, Set.image_singleton]
  have hc' : Nat.card (centralizer ({eN tN} : Set (PSL2 F))) = 4 := by
    rw [← hmap, card_map_of_injective eN.injective]
    exact hc
  rcases Theory.PSL2.involution_centralizer_card_cases hF (eN tN) htI with h | h
  · right
    rw [hc'] at h
    omega
  · left
    rw [hc'] at h
    omega

end Theory.GroupTheory.DihedralEightCentralizer
