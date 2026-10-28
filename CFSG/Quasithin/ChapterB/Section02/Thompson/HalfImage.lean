module
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Sylow
public import Theory.GroupTheory.SylowImageLocalization

/-!
# Half-order image lifts into the near-maximum Thompson subgroup

Pull back a subgroup of index at most two in a maximum elementary image.
Its lift loses at most one rank. After conjugation, localization by an
element of the full action kernel places the lift in the original Sylow
without changing either its order or its image. Its image therefore lies
in J₁'s image. Neither surjectivity nor a two-group kernel is assumed.
SixThompsonImage uses this with the actual even six-letter conjugators.
Source: Aschbacher–Smith 13.2.2(10), p.878, and B.2.2, p.74.
-/

public noncomputable section
open Subgroup
open Stellmacher
namespace CFSG.Quasithin.ChapterB
variable {G H : Type*} [Group G] [Finite G] [Group H]

theorem near_maximum_image_le_thompson_one
    (T : Sylow 2 G) (q : G →* H) (hr : 1 < twoRank (T : Subgroup G))
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hcard : 2 ^ (twoRank (T : Subgroup G) - 1) ≤ Nat.card A)
    (hAT : A.map q ≤ (T : Subgroup G).map q) :
    A.map q ≤ (thompsonJ (T : Subgroup G) 1).map q := by
  obtain ⟨k,hk,hBT⟩ := T.exists_kernel_conjugate_le q A
    (IsElementaryAbelian.isPGroup 2 A) hAT
  let B := A.map (MulAut.conj k).toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBq : B.map q = A.map q := by
    rw [map_map]
    have he : q.comp (MulAut.conj k).toMonoidHom = q := by
      ext x
      simp [MulAut.conj_apply,hk]
    rw [he]
  have hBc : Nat.card B = Nat.card A := card_map_of_injective (MulAut.conj k).injective
  rw [←hBq]
  apply map_mono
  intro b hb
  obtain ⟨E,hEB,hEe,hEc,hbE⟩ := IsElementaryAbelian.exists_two_power_subgroup_mem B
    (by omega : 0 < twoRank (T : Subgroup G) - 1) (hBc.symm ▸ hcard) b hb
  exact (le_sSup (show E ∈ thompsonFamily (T : Subgroup G) 1 from
    ⟨hEB.trans hBT,hEe,by omega,hEc⟩)) hbE

theorem maximum_half_image_conjugate_le_thompson_one
    [Finite H] (T : Sylow 2 G) (q : G →* H)
    (hr : 1 < twoRank (T : Subgroup G))
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G))
    (C : Subgroup H) (hC : C ≤ A.map q) (hc : Nat.card (A.map q) ≤ 2 * Nat.card C)
    (g : H) (hg : g ∈ q.range)
    (hCT : C.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G).map q) :
    C.map (MulAut.conj g).toMonoidHom ≤ (thompsonJ (T : Subgroup G) 1).map q := by
  let := hA.2.1
  let B := A ⊓ C.comap q
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective (inclusion (show B ≤ A from inf_le_left)) (inclusion_injective _)
  have hBq : B.map q = C := by
    apply le_antisymm
    · rintro y ⟨x,hx,rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨x,hx,hxy⟩ := hC hy
      exact ⟨x,⟨hx,show q x ∈ C from hxy.symm ▸ hy⟩,hxy⟩
  have hi : B.relIndex A ≤ 2 := by
    have he : B.relIndex A = C.relIndex (A.map q) := by
      rw [inf_relIndex_left,relIndex_comap]
    rw [he]
    have hm := relIndex_mul_relIndex (⊥ : Subgroup H) C (A.map q) bot_le hC
    simp only [relIndex_bot_left] at hm
    have hp : 0 < Nat.card C := Nat.card_pos
    nlinarith
  have hcard : Nat.card A ≤ 2 * Nat.card B := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup G) B A bot_le inf_le_left
    simp only [relIndex_bot_left] at hm
    nlinarith
  obtain ⟨x,rfl⟩ := hg
  let E := B.map (MulAut.conj x).toMonoidHom
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hEq : E.map q = C.map (MulAut.conj (q x)).toMonoidHom := by
    calc
      _ = (B.map q).map (MulAut.conj (q x)).toMonoidHom := by
        rw [map_map,map_map]
        congr 1
        ext b
        simp [MulAut.conj_apply]
      _ = _ := by rw [hBq]
  have hec : 2 ^ (twoRank (T : Subgroup G) - 1) ≤ Nat.card E := by
    rw [card_map_of_injective (MulAut.conj x).injective]
    rw [elementaryAbelianMaxSubgroups_card_eq _ _ hA,maxOrder_eq_two_pow_rank] at hcard
    have he : twoRank (T : Subgroup G) = (twoRank (T : Subgroup G) - 1) + 1 := by omega
    rw [he,pow_succ] at hcard
    omega
  rw [←hEq]
  exact near_maximum_image_le_thompson_one T q hr E hec (hEq.symm ▸ hCT)

end CFSG.Quasithin.ChapterB
