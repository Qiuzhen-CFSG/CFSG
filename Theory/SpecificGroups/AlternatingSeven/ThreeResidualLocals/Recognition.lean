module

public import GorensteinWalter.NormalKleinFourIndexThree
import Theory.GroupTheory.SpecificGroups.DihedralAut
public import Theory.ElementaryAbelian.Basic

/-!
# Recognizing the three-generated subgroup in A7

A normal elementary four-group on which a three-generated subgroup acts with
full commutator is its two-core. Indeed, the core embeds in a Sylow two-group
of A7 and has order four or eight. In the order-eight case it is dihedral, and
its automorphism group is a two-group, so every order-three generator centralizes
it. This contradicts the full commutator. Index three then gives a genuine A4
isomorphism through the faithful four-point action.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, 15.3.43(a),(b),
and the A7 paragraph on printed p.1140 (combined manuscript, 1 March 2004).
-/

public section

open Subgroup
open scoped commutatorElement
namespace AlternatingSeven.ThreeResidualLocals

private theorem sylow_card (S : Sylow 2 (alternatingGroup (Fin 7))) :
    Nat.card S = 8 := by
  rw [S.card_eq_multiplicity, nat_card_alternatingGroup, Nat.card_eq_fintype_card]
  norm_num [Nat.factorial]
  rw [show (2520 : ℕ).factorization 2 = 3 by
    rw [show 2520 = 2 ^ 3 * 315 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    simp [Nat.prime_two.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]]
  norm_num

private theorem two_subgroup_card_dvd_eight
    (Q : Subgroup (alternatingGroup (Fin 7))) (hQ : IsPGroup 2 Q) :
    Nat.card Q ∣ 8 := by
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  rw [← sylow_card S]
  exact card_dvd_of_le hS

private theorem two_subgroup_card_eight_equiv
    (Q : Subgroup (alternatingGroup (Fin 7))) (hQ : IsPGroup 2 Q)
    (hc : Nat.card Q = 8) : Nonempty (Q ≃* DihedralGroup 4) := by
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  have heq : Q = (S : Subgroup (alternatingGroup (Fin 7))) :=
    eq_of_le_of_card_ge hS (by rw [hc, sylow_card S])
  obtain ⟨m, _, ⟨e⟩⟩ := GorensteinWalter.hasDihedralSylowTwo_alternatingGroupSeven S
  have hm : m = 2 := by
    have hcS := Nat.card_congr e.toEquiv
    rw [sylow_card S, DihedralGroup.nat_card] at hcS
    have hp : 2 ^ m = 2 ^ 2 := by omega
    exact Nat.pow_right_injective (by decide : 1 < 2) hp
  subst m
  exact ⟨(MulEquiv.subgroupCongr heq).trans e⟩

private theorem hom_eq_one_of_order_three
    {G H : Type*} [Group G] [Group H] (hH : IsPGroup 2 H)
    (f : G →* H) {g : G} (hg : orderOf g = 3) : f g = 1 := by
  have hd : orderOf (f g) ∣ 3 := hg ▸ orderOf_map_dvd f g
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hH.orderOf_coprime (by decide : Nat.Coprime 2 3) (f g))
      dvd_rfl hd)

private theorem centralizer_eq_of_four_index_three
    {G : Type*} [Group G] [Finite G] (W : Subgroup G)
    (hW : IsKleinFour W) (hidx : W.index = 3) (hcomm : ⁅W, ⊤⁆ = W) :
    centralizer (W : Set G) = W := by
  let : IsKleinFour W := hW
  have hWC : W ≤ centralizer (W : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr IsKleinFour.isMulCommutative
  have hd : (centralizer (W : Set G)).index ∣ 3 := by
    rw [← hidx]
    exact index_dvd_of_le hWC
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with h | h
  · have htop : centralizer (W : Set G) = ⊤ := index_eq_one.mp h
    have hb : W = ⊥ := by
      rw [← hcomm, commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr (by rw [htop])
    have hc := hW.card_four
    simp [hb] at hc
  · have hr : W.relIndex (centralizer (W : Set G)) = 1 := by
      have he := relIndex_mul_index hWC
      rw [h, hidx] at he
      omega
    exact le_antisymm (relIndex_eq_one.mp hr) hWC

/-- A normal four-group moved by the full three-generated subgroup is its two-core. -/
theorem twoCore_eq_plane
    (Y V : Subgroup (alternatingGroup (Fin 7)))
    (hVY : V ≤ Y) (hVN : (V.subgroupOf Y).Normal)
    (hVE : IsElementaryAbelian 2 V) (hVc : Nat.card V = 4)
    (hcomm : ⁅V, Y⁆ = V)
    (hgen : closure {y : alternatingGroup (Fin 7) | y ∈ Y ∧ orderOf y = 3} = Y) :
    pCore 2 Y = V.subgroupOf Y := by
  let : IsElementaryAbelian 2 V := hVE
  let : (V.subgroupOf Y).Normal := hVN
  let : IsElementaryAbelian 2 (V.subgroupOf Y) := IsElementaryAbelian.subgroupOf hVY
  have hWQ : V.subgroupOf Y ≤ pCore 2 Y :=
    le_sSup ⟨hVN, IsElementaryAbelian.isPGroup 2 (V.subgroupOf Y)⟩
  have hWc : Nat.card (V.subgroupOf Y) = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVY).toEquiv, hVc]
  let Q := pCore 2 Y
  let E := Q.map Y.subtype
  have hEc : Nat.card E = Nat.card Q := card_map_of_injective Y.subtype_injective
  have hEp : IsPGroup 2 E := pCore_isPGroup.map Y.subtype
  have hQdvd : Nat.card Q ∣ 8 := by
    rw [← hEc]
    exact two_subgroup_card_dvd_eight E hEp
  have hfour : 4 ∣ Nat.card Q := by
    rw [← hWc]
    exact card_dvd_of_le hWQ
  have hQfour : Nat.card Q = 4 := by
    have hcases : Nat.card Q = 4 ∨ Nat.card Q = 8 := by
      have hpos := Nat.card_pos (α := Q)
      have hle := Nat.le_of_dvd (by decide : 0 < 8) hQdvd
      have hge := Nat.le_of_dvd hpos hfour
      omega
    rcases hcases with h | h
    · exact h
    · exfalso
      obtain ⟨eE⟩ := two_subgroup_card_eight_equiv E hEp (hEc.trans h)
      let e : Q ≃* DihedralGroup 4 :=
        (equivMapOfInjective Q Y.subtype Y.subtype_injective).trans eE
      have hAut : IsPGroup 2 (MulAut Q) :=
        (DihedralGroup.isPGroup_mulAut_of_two_lt (by decide : 2 < 4)
          (IsPGroup.of_card (n := 3) (by rw [DihedralGroup.nat_card]; norm_num))).of_equiv
            (MulAut.congr e).symm
      have hYC : Y ≤ centralizer (V : Set (alternatingGroup (Fin 7))) := by
        rw [← hgen]
        apply (closure_le _).2
        rintro y ⟨hy, h3⟩
        let yY : Y := ⟨y, hy⟩
        have hy3 : orderOf yY = 3 := by
          rw [← orderOf_injective Y.subtype Y.subtype_injective]
          exact h3
        have hact : MulAut.conjNormal (H := Q) yY = 1 :=
          hom_eq_one_of_order_three hAut _ hy3
        apply mem_centralizer_iff.mpr
        intro v hv
        let vQ : Q := ⟨⟨v, hVY hv⟩, hWQ hv⟩
        have hvfix := congrArg (fun a : MulAut Q => a vQ) hact
        have hval := congrArg (fun x : Q => ((x : Y) : alternatingGroup (Fin 7))) hvfix
        change y * v * y⁻¹ = v at hval
        exact (mul_inv_eq_iff_eq_mul.mp hval).symm
      have hb : V = ⊥ := by
        rw [← hcomm, commutator_comm]
        exact commutator_eq_bot_iff_le_centralizer.mpr hYC
      simp [hb] at hVc
  exact (eq_of_le_of_card_ge hWQ (by rw [hWc, hQfour])).symm

/-- Intrinsic A4 recognition in A7, without an assumed order or stabilizer type. -/
theorem residual_mulEquiv_alternating_four
    (Y V : Subgroup (alternatingGroup (Fin 7)))
    (hVY : V ≤ Y) (hVN : (V.subgroupOf Y).Normal)
    (hVE : IsElementaryAbelian 2 V) (hVc : Nat.card V = 4)
    (hcomm : ⁅V, Y⁆ = V) (hidx : (pCore 2 Y).index = 3)
    (hgen : closure {y : alternatingGroup (Fin 7) | y ∈ Y ∧ orderOf y = 3} = Y) :
    Nonempty (Y ≃* alternatingGroup (Fin 4)) := by
  let W := V.subgroupOf Y
  have hWc : Nat.card W = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVY).toEquiv, hVc]
  let : IsElementaryAbelian 2 V := hVE
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVY
  let : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hWK : IsKleinFour W := ⟨hWc, IsElementaryAbelian.exponent_eq_prime⟩
  have hWi : W.index = 3 := by
    change (V.subgroupOf Y).index = 3
    rw [← twoCore_eq_plane Y V hVY hVN hVE hVc hcomm hgen]
    exact hidx
  have hWcomm : ⁅W, ⊤⁆ = W := by
    apply (map_injective (f := Y.subtype) Y.subtype_injective)
    rw [map_commutator, map_subgroupOf_eq_of_le hVY,
      ← MonoidHom.range_eq_map, Y.range_subtype, hcomm]
  exact GorensteinWalter.mulEquiv_alternatingGroup_four_of_normal_kleinFour_index_three
    W hVN hWK (centralizer_eq_of_four_index_three W hWK hWi hWcomm) hWi

end AlternatingSeven.ThreeResidualLocals
