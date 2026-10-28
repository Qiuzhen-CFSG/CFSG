module

public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.Amalgam.DihedralTwelvePair.Models

/-!
# A group of order twelve with a normal symmetric-three subgroup

Every automorphism of S₃ is inner and its center is trivial. A normal S₃
therefore splits off its ambient centralizer. At ambient order twelve that
centralizer has order two, and the resulting product is D₁₂. This determines
the actual quotient over the C₄² radical in the full binary G₂ parabolic.

Source: the elementary quotient calculation in Aschbacher–Smith F.6.18(11).
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
open NormalSymmetricThreePairRank RankTwoAmalgam

/-- A normal S₃ in order twelve gives the dihedral group of order twelve. -/
theorem dihedral_twelve_of_normal_symmetric_three
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 12)
    (H : Subgroup G) [H.Normal] (j : H ≃* Equiv.Perm (Fin 3)) :
    Nonempty (G ≃* DihedralGroup 6) := by
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
  let m : H × C ≃* G := e.trans ((MulEquiv.subgroupCongr hs).trans (Subgroup.topEquiv))
  have hH : Nat.card H = 6 := by
    rw [Nat.card_congr j.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hC : Nat.card C = 2 := by
    have hc := Nat.card_congr m.toEquiv
    rw [Nat.card_prod,hH,hG] at hc
    omega
  let eC : C ≃* swapMiddle := mulEquivOfPrimeCardEq hC swapMiddle_card
  exact ⟨(((m.symm.trans MulEquiv.prodComm).trans (eC.prodCongr j)).trans
    dihedralTwelveVertexEquiv)⟩

end Theory.GroupTheory
