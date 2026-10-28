module

public import Theory.SpecificGroups.GL2.ThreeResidualImages.Generation
public import Theory.SpecificGroups.SL2.BinaryTetrahedralQuotient
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding

/-!
# Two ternary cubic actions and an involutory inverter

On an elementary ternary plane, two distinct nontrivial three-group images
are cubic and generate SL₂(3). An involution inverting a nontrivial cubic
cannot have determinant one, because the determinant-one involutions are
scalar. It therefore extends this action to GL₂(3), forcing a factor16 in
the actor group order. The scalar test is a single kernel calculation on
81 matrices; all generation is reused from the existing cubic-pair theorem.
Source: Aschbacher, Sporadic Groups (1994),45.9,printed p246.
-/

public section
open Matrix Subgroup
namespace Matrix.GeneralLinearGroup
private theorem special_square_scalar : ∀ A:Matrix (Fin 2) (Fin 2) (ZMod 3),
    A.det=1→A^2=1→A=1 ∨ A= -1 := by decide
 theorem three_special_square_commutes (t x:GL (Fin 2) (ZMod 3))
    (ht:t∈threeSpecialLinear) (ht2:t^2=1) : Commute t x := by
  have hs:=special_square_scalar t.val ((three_mem_specialLinear t).mp ht) (congrArg Units.val ht2)
  apply Units.ext
  rcases hs with hs|hs
  · simp [hs]
  · simp [hs]
 theorem three_cubic_pair_inverter_generate (H C D:Subgroup (GL (Fin 2) (ZMod 3)))
    (hC:Nat.card C=3) (hD:Nat.card D=3) (hne:C≠D) (hCH:C≤H) (hDH:D≤H)
    (t x:GL (Fin 2) (ZMod 3)) (ht:t∈H) (ht2:t^2=1)
    (hx3:x^3=1) (hx1:x≠1) (hinv:t*x*t⁻¹=x⁻¹) : H=⊤ := by
  have hSH:threeSpecialLinear≤H:=(three_distinct_cubic_join C D hC hD hne).symm.le.trans (sup_le hCH hDH)
  have htS:t∉threeSpecialLinear:=by
    intro htS
    have he:t*x*t⁻¹=x:=by rw [(three_special_square_commutes t x htS ht2).eq,mul_inv_cancel_right]
    have hx2:x^2=1:=by
      have hi:x=x⁻¹:=he.symm.trans hinv
      rw [pow_two]
      nth_rw 1 [hi]
      exact inv_mul_cancel x
    have hd:=Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx2) (orderOf_dvd_of_pow_eq_one hx3)
    exact hx1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by simpa using hd)))
  have hSc:Nat.card threeSpecialLinear=24:=
    (Nat.card_congr threeSpecialLinearEquiv.toEquiv).trans
      ((Nat.card_congr GLS3.Chapter5.SchurPresentation.binaryTetrahedralEquivSL.toEquiv).symm.trans
        GLS3.Chapter5.SchurPresentation.binaryTetrahedral_card)
  have hGc:Nat.card (GL (Fin 2) (ZMod 3))=48:=by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ,ZMod.card]
  have hcard:Nat.card H=48:=by
    have hd:24∣Nat.card H:=hSc ▸ card_dvd_of_le hSH
    obtain ⟨k,hk⟩:=hd
    have hlo:24≤Nat.card H:=hSc ▸ card_le_of_le hSH
    have hup:Nat.card H≤48:=hGc ▸ Nat.card_le_card_of_injective H.subtype H.subtype_injective
    have hnot:Nat.card H≠24:=by
      intro hh
      have he:threeSpecialLinear=H:=eq_of_le_of_card_ge hSH (by rw [hSc,hh])
      exact htS (he.ge ht)
    omega
  exact eq_top_of_card_eq H (hcard.trans hGc.symm)
end Matrix.GeneralLinearGroup

namespace MulAut
variable {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 3 A]
theorem ternary_plane_cubic_card (hA : Nat.card A=9) (C : Subgroup (MulAut A))
    (hC : IsPGroup 3 C) (hne:C≠⊥) : Nat.card C=3 := by
  obtain ⟨f,hf⟩:=IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p:=3) (n:=2) A (by omega)
  have hGL:Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))=48:=by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ,ZMod.card]
  have hd:Nat.card C∣48:=by
    have hh:=(C.map f).card_subgroup_dvd_card
    rwa [card_map_of_injective hf,hGL] at hh
  obtain ⟨n,hn⟩:=hC.exists_card_eq
  have hn2:n<2:=by
    by_contra hh
    have h9:9∣48:=(Nat.pow_dvd_pow 3 (Nat.le_of_not_gt hh)).trans (hn ▸ hd)
    norm_num at h9
  interval_cases n
  · exact (hne (card_eq_one.mp (by simpa using hn))).elim
  · simpa using hn

theorem ternary_plane_two_cubics_inverter (hA : Nat.card A=9)
    (H C D : Subgroup (MulAut A)) (hC:IsPGroup 3 C) (hD:IsPGroup 3 D)
    (hCne:C≠⊥) (hDne:D≠⊥) (hne:C≠D) (hCH:C≤H) (hDH:D≤H)
    (t x : MulAut A) (ht:t∈H) (ht2:t^2=1) (hx:x∈C) (hx1:x≠1)
    (hi:t*x*t⁻¹=x⁻¹) : 16∣Nat.card H := by
  obtain ⟨f,hf⟩:=IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p:=3) (n:=2) A (by omega)
  have hCc:Nat.card C=3:=ternary_plane_cubic_card hA C hC hCne
  have hDc:Nat.card D=3:=ternary_plane_cubic_card hA D hD hDne
  have hCD:C.map f≠D.map f:=by
    intro he
    apply hne
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,heq⟩:=he.le (mem_map_of_mem f hx)
      exact hf heq ▸ hy
    · intro hx
      obtain ⟨y,hy,heq⟩:=he.ge (mem_map_of_mem f hx)
      exact hf heq ▸ hy
  have hx3:x^3=1:=by
    have hh:=pow_card_eq_one' (x:=(⟨x,hx⟩:C))
    rw [hCc] at hh
    exact congrArg Subtype.val hh
  have he: H.map f=⊤:=Matrix.GeneralLinearGroup.three_cubic_pair_inverter_generate
    (H.map f) (C.map f) (D.map f)
    ((card_map_of_injective hf).trans hCc) ((card_map_of_injective hf).trans hDc)
    hCD (map_mono hCH) (map_mono hDH) (f t) (f x) (mem_map_of_mem f ht)
    (by rw [←map_pow,ht2,map_one]) (by rw [←map_pow,hx3,map_one])
    (fun hh=>hx1 (hf (hh.trans (map_one f).symm)))
    (by simpa only [map_mul,map_inv] using congrArg f hi)
  have hc:Nat.card H=48:=by
    rw [←card_map_of_injective (K:=H) hf,he,card_top,Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ,ZMod.card]
  rw [hc]
  decide
end MulAut
