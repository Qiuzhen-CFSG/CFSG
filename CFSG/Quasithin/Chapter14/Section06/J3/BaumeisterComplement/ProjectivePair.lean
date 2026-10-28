module
public import CFSG.Quasithin.Chapter14.Section06.J3.BaumeisterComplement.FiveLocal
public import Theory.SpecificGroups.AlternatingSix.OuterInvolutionExtension.PGLComparison
public import GorensteinWalter.PGL2LowTorus
public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral

/-!
# An outer involution centralizing the literal dihedral quotient image

The low-two-part torus of PGL₂(9) has order ten. Its odd subgroup and an
inner reflector give D₁₀ inside the derived A₆, centralized by the outer
torus involution. Sylow-five conjugacy in A₆ aligns this subgroup with any
specified order-ten subgroup. Transport retains the given projective
isomorphism and the actual index-two subgroup.

This is the quotient calculation in Baumeister, *A geometry for groups
of J₃-type* (2007), Lemma 2.5, p.496. `Pair` lifts this involution through
the same-cubic complement and applies it to the literal second parabolic.
-/

open Subgroup GorensteinWalter
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
public noncomputable section
open Atlas.Comparisons.Exceptional
local notation "F" => Nine.F
local notation "X" => PGL2 F
local instance : Finite X := Finite.of_surjective Matrix.ProjGenLinGroup.mk
  Matrix.ProjGenLinGroup.mk_surjective

private theorem nine_odd : IsOddPrimePower (Nat.card F) := by
  rw [Nine.card]
  exact ⟨3, 2, by decide, by decide, by decide, by decide⟩

private theorem nine_gt : 3 < Nat.card F := by rw [Nine.card]; decide

private theorem projective_ten_actor_model :
    ∃ (B : Subgroup X) (a : X), Nat.card B = 10 ∧
      B ≤ commutator X ∧ orderOf a = 2 ∧ a ∉ commutator X ∧
      B ≤ centralizer ({a} : Set X) := by
  obtain ⟨U,a,t,w,hcyc,hodd,hcard,haU,haout,hane,ha2,htJ,htU,ht2,
    htinv,htw,hwU,hw2,hwinv,hcent⟩ :=
    pgl2_low_two_part_torus_reflection_data F nine_odd nine_gt
  have hU : Nat.card U = 10 := by
    rw [Nine.card] at hcard
    rcases hcard with hcard | hcard
    · rw [hcard] at hodd
      norm_num [Nat.odd_iff] at hodd
    · exact hcard
  let J := commutator X
  have hJi : J.index = 2 := by
    rw [show J = (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
      from pgl2_commutator_eq_psl2_range_of_card_gt_three F nine_odd nine_gt]
    exact pgl2_psl2Range_index_eq_two F nine_odd
  let R := U ⊓ J
  have hi : (J.subgroupOf U).index = 2 := by
    have hd := J.relIndex_dvd_index_of_normal U
    rw [hJi] at hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd with hd | hd
    · have hh : U ≤ J := relIndex_eq_one.mp hd
      exact (haout (hh haU)).elim
    · exact hd
  have hR : Nat.card R = 5 := by
    have hh := (J.subgroupOf U).index_mul_card
    have he : Nat.card (J.subgroupOf U) = Nat.card R := by
      rw [← inf_subgroupOf_left]
      exact Nat.card_congr (subgroupOfEquivOfLe (show U ⊓ J ≤ U from inf_le_left)).toEquiv
    rw [hi,he,hU] at hh
    omega
  have hRcyc : IsCyclic R := by
    let : IsCyclic U := hcyc
    exact isCyclic_of_injective (inclusion (show R ≤ U from inf_le_left))
      (inclusion_injective _)
  obtain ⟨e⟩ := nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted R t hRcyc
    (by simpa [pow_two] using ht2) (fun hh => htU hh.1) (fun x hx => htinv x hx.1)
  refine ⟨R ⊔ zpowers t,a,?_,sup_le inf_le_right (zpowers_le.mpr htJ),
    orderOf_eq_prime (by simpa [pow_two] using ha2) hane,haout,?_⟩
  · rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card,hR]
  · apply sup_le
    · intro x hx
      let : IsCyclic U := hcyc
      let : CommGroup U := IsCyclic.commGroup
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mul_comm (⟨x,hx.1⟩ : U) ⟨a,haU⟩))
    · apply zpowers_le.mpr
      apply mem_centralizer_singleton_iff.mpr
      have hh := htinv a haU
      rw [inv_eq_of_mul_eq_one_right ha2] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh

/-- Every order-ten subgroup in the derived A₆ of PGL₂(9) is centralized
by an outer involution. -/
theorem projective_ten_actor (B : Subgroup X) (hB : Nat.card B = 10)
    (hBJ : B ≤ commutator X) :
    ∃ a : X, orderOf a = 2 ∧ a ∉ commutator X ∧
      B ≤ centralizer ({a} : Set X) := by
  let J := commutator X
  have hJ : J = (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three F nine_odd nine_gt
  let e : J ≃* alternatingGroup (Fin 6) := (MulEquiv.subgroupCongr hJ).trans
    ((psl2EquivToPGLRange F).symm.trans psl2NineCoordinatesEquivAlt6)
  obtain ⟨E,a,hE,hEJ,ha,haout,hEa⟩ := projective_ten_actor_model
  let E6 := (E.subgroupOf J).map e.toMonoidHom
  let B6 := (B.subgroupOf J).map e.toMonoidHom
  have hE6 : Nat.card E6 = 10 := (card_map_of_injective e.injective).trans
    ((Nat.card_congr (subgroupOfEquivOfLe hEJ).toEquiv).trans hE)
  have hB6 : Nat.card B6 = 10 := (card_map_of_injective e.injective).trans
    ((Nat.card_congr (subgroupOfEquivOfLe hBJ).toEquiv).trans hB)
  obtain ⟨g,hg⟩ := ten_conjugate E6 B6 hE6 hB6
  let k : J := e.symm g
  let c := MulAut.conj (k : X)
  have hle : E.map c.toMonoidHom ≤ B := by
    rintro _ ⟨x,hx,rfl⟩
    have hx6 : e ⟨x,hEJ hx⟩ ∈ E6 := mem_map_of_mem e.toMonoidHom hx
    have hh : g * e ⟨x,hEJ hx⟩ * g⁻¹ ∈ B6 :=
      hg ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hx6
    have hk : e (k * ⟨x,hEJ hx⟩ * k⁻¹) = g * e ⟨x,hEJ hx⟩ * g⁻¹ := by simp [k]
    rw [← hk,mem_map_equiv] at hh
    have hh' := show k * ⟨x,hEJ hx⟩ * k⁻¹ ∈ B.subgroupOf J from
      by simpa only [e.symm_apply_apply] using hh
    exact hh'
  have hEB : E.map c.toMonoidHom = B := eq_of_le_of_card_ge hle (by
    rw [card_map_of_injective c.injective,hE,hB])
  refine ⟨c a,(c.orderOf_eq a).trans ha,?_,?_⟩
  · intro hh
    have hh' := J.mul_mem (J.mul_mem (J.inv_mem k.property) hh) k.property
    have he : (k : X)⁻¹ * c a * k = a := by dsimp [c]; group
    exact haout (he ▸ hh')
  · rw [← hEB]
    rintro _ ⟨x,hx,rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      ((show Commute x a from mem_centralizer_singleton_iff.mp (hEa hx)).map
        c.toMonoidHom).eq

/-- The outer centralizing involution transported through a specified PGL₂(9)
isomorphism and an actual index-two subgroup. -/
theorem ten_actor_of_projective {H : Type*} [Group H] [Finite H]
    (L B : Subgroup H) (hL : L.index = 2) (hBL : B ≤ L)
    (hB : Nat.card B = 10) (e : H ≃* X) :
    ∃ a : H, orderOf a = 2 ∧ a ∉ L ∧ B ≤ centralizer ({a} : Set H) := by
  let L9 := L.map e.toMonoidHom
  have hL9 : L9.index = 2 := (index_map_equiv L e).trans hL
  let : L9.Normal := normal_of_index_eq_two hL9
  let : IsCyclic (X ⧸ L9) := isCyclic_of_prime_card (p := 2) hL9
  have hJL : commutator X ≤ L9 := Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hJi : (commutator X).index = 2 := by
    rw [pgl2_commutator_eq_psl2_range_of_card_gt_three F nine_odd nine_gt]
    exact pgl2_psl2Range_index_eq_two F nine_odd
  have heq : commutator X = L9 := eq_of_le_of_card_ge hJL (by
    have h1 := (commutator X).index_mul_card
    have h2 := L9.index_mul_card
    rw [hJi] at h1
    rw [hL9] at h2
    omega)
  obtain ⟨a,ha,haout,hBa⟩ := projective_ten_actor (B.map e.toMonoidHom)
    ((card_map_of_injective e.injective).trans hB)
    (heq.symm ▸ map_mono hBL)
  refine ⟨e.symm a,(e.symm.orderOf_eq a).trans ha,?_,?_⟩
  · intro hh
    apply haout
    rw [heq]
    have hh' := mem_map_of_mem e.toMonoidHom hh
    change e (e.symm a) ∈ L9 at hh'
    simpa only [e.apply_symm_apply] using hh'
  · intro b hb
    have hh : Commute (e b) a := mem_centralizer_singleton_iff.mp
      (hBa (mem_map_of_mem e.toMonoidHom hb))
    exact mem_centralizer_singleton_iff.mpr (by
      simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using (hh.map e.symm.toMonoidHom).eq)

end
end CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
