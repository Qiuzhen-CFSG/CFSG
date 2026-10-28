module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.OneAbelian
public import Theory.GroupTheory.TwoPerfectElementaryIndexTwo
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.NormalSixteenC4SquareRecognition
public import Theory.ElementaryAbelian.Injective

/-!
# The abelian core in the original order-thirty-two amalgam

An elementary first core forces overlap order at most sixteen. Otherwise the
core intersection is an elementary subgroup of index two in the nonabelian
opposite core. The opposite two-residual normalizes that intersection; the
common Sylow does also, so it is normal in the entire opposite vertex. Its
centralizer would then be a normal two-group containing the first core,
contradicting faithfulness.

In the remaining F.6.5 branch the previously proved source bound gives a
center-free vertex with abelian core of order sixteen. The exclusion above
supplies an element of order four. The normal order-sixteen recognition theorem
therefore identifies this actual core with C₄ × C₄.

Source: Aschbacher–Smith F.1.12(I)(8) and F.6.5, printed pp.263 and 305.
This identifies the original core; recognition of the whole vertices and the
compatible G₂(2)′ amalgam is a separate source step.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.SourceAssembly.OneAbelian
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

private theorem core_half (h : IsGoldschmidtTriple A B) :
    2*Nat.card (pCore 2 A)=Nat.card (A⊓B : Subgroup G) := by
  have ha := h.local_card_eq_three_mul_intersection
  have hb := SymmetricThreeTwoCore.card_eq h.quotient_left.some
  omega

/-- An elementary core cannot occur in a large faithful binary pair. -/
theorem intersection_card_le_sixteen_of_elementary
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    [IsElementaryAbelian 2 (pCore 2 A)] : Nat.card (A⊓B : Subgroup G)≤16 := by
  by_contra! hlarge
  have hnb : ¬ IsMulCommutative (pCore 2 B) := by
    intro hb
    let := hb
    have hh := BothAbelian.intersection_card_le_sixteen h hcore hA hB
    omega
  let R := pCore 2 B
  let Q := (pCore 2 A).map A.subtype
  let D := Q.subgroupOf B
  let J := D ⊓ R
  have hQA : Q≤A⊓B := h.local_twoCore_le_intersection
  have hDb : D.map B.subtype=Q := map_subgroupOf_eq_of_le (hQA.trans inf_le_right)
  have hDc : Nat.card D=Nat.card R := by
    have hh := core_half h
    have hr := core_half h.symm
    rw [inf_comm B A] at hr
    rw [Nat.card_congr (subgroupOfEquivOfLe (hQA.trans inf_le_right)).toEquiv,
      card_map_of_injective A.subtype_injective]
    change Nat.card (pCore 2 A)=Nat.card (pCore 2 B)
    omega
  have hnot : ¬ D≤R := by
    intro he
    have heq : D=R := eq_of_le_of_card_ge he hDc.symm.le
    have hQA' : A≤normalizer (Q : Set G) := h.left_core_normalized
    have hQB' : B≤normalizer (Q : Set G) := by
      rw [←hDb,heq]
      exact h.symm.left_core_normalized
    have hbot := h.common_normal_eq_bot hcore Q hQA
      ((normal_subgroupOf_iff_le_normalizer (hQA.trans inf_le_left)).mpr hQA')
      ((normal_subgroupOf_iff_le_normalizer (hQA.trans inf_le_right)).mpr hQB')
    have hh := core_half h
    have hQc : Nat.card Q=Nat.card (pCore 2 A) := card_map_of_injective A.subtype_injective
    rw [←hQc,hbot,card_bot] at hh
    omega
  obtain ⟨S,hS⟩ := h.intersection_sylow
  let T := S.subtype (hS.symm.le.trans inf_le_right)
  have hDleT : D≤(T : Subgroup B) := by
    intro d hd
    change (d : G)∈(S : Subgroup G)
    exact hS ▸ hQA hd
  have hRT : R≤(T : Subgroup B) := pCore_isPGroup.le_sylow_of_normal T
  have hiRT : (R.subgroupOf (T : Subgroup B)).index=2 := by
    change R.relIndex ((S : Subgroup G).subgroupOf B)=2
    have hi := h.symm.left_core_index
    rw [inf_comm B A,hS] at hi
    have he := relIndex_map_map_of_injective R ((S : Subgroup G).subgroupOf B) B.subtype_injective
    rw [map_subgroupOf_eq_of_le (hS.symm.le.trans inf_le_right)] at he
    exact he.symm.trans hi
  have hJindex : (J.subgroupOf R).index=2 := by
    have hd : ¬ D.subgroupOf (T : Subgroup B)≤R.subgroupOf (T : Subgroup B) := by
      intro hh
      exact hnot (fun d hd => hh (show (⟨d,hDleT hd⟩ : (T : Subgroup B))∈D.subgroupOf _ from hd))
    have hi := (R.subgroupOf (T : Subgroup B)).subgroupOf_index_eq_two
      (D.subgroupOf (T : Subgroup B)) hiRT hd
    have hcount := (R.subgroupOf D).index_mul_card
    have hid : (R.subgroupOf D).index=2 := by
      change (R.subgroupOf (T : Subgroup B)).relIndex (D.subgroupOf (T : Subgroup B))=2 at hi
      rw [relIndex_subgroupOf hDleT] at hi
      exact hi
    rw [hid,hDc] at hcount
    have hmap : Nat.card (R.subgroupOf D)=Nat.card J := by
      rw [← card_map_of_injective D.subtype_injective, subgroupOf_map_subtype]
      exact Nat.card_congr (MulEquiv.subgroupCongr (inf_comm R D)).toEquiv
    have hcount' := (J.subgroupOf R).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (show J≤R from inf_le_right)).toEquiv] at hcount'
    rw [hmap] at hcount
    have hp := Nat.card_pos (α := J)
    nlinarith
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.subgroupOf (hQA.trans inf_le_right)
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.of_injective
    (inclusion inf_le_left) (inclusion_injective inf_le_left)
  have hres : pResidual 2 B≤normalizer (J : Set B) :=
    twoPerfect_le_normalizer_elementary_index_two _ R J (isPPerfect_pResidual 2)
      (by rw [R.normalizer_eq_top];exact le_top) inf_le_right inferInstance hJindex
      (fun he => hnb he.toIsMulCommutative)
  have hTD : (T : Subgroup B)≤normalizer (D : Set B) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro d
    have htG : (t : G)∈(S : Subgroup G) := ht
    exact mem_normalizer_iff.mp (h.left_core_normalized ((hS.symm ▸ htG).1)) d
  have hTJ : (T : Subgroup B)≤normalizer (J : Set B) :=
    (le_inf hTD (by rw [R.normalizer_eq_top];exact le_top)).trans inf_normalizer_le_normalizer_inf
  have hJN : J.Normal := normalizer_eq_top_iff.mp
    (top_unique ((pResidual_sup_sylow_eq_top T) ▸ sup_le hres hTJ))
  let := hJN
  have hCp := centralizer_isPGroup_of_index_two_in_core (h.symm.local_core_selfCentralizing hB) J hJindex
  have hCD : centralizer (J : Set B)≤R := le_sSup ⟨inferInstance,hCp⟩
  exact hnot (D.le_centralizer.trans ((centralizer_le inf_le_left).trans hCD))

/-- The actual abelian local core in the remaining source branch is a square
of cyclic four-groups. -/
theorem abelian_core_equiv_c4_square
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G=⊥)
    (hA : generalizedFitting A=pCore 2 A) (hB : generalizedFitting B=pCore 2 B)
    [IsMulCommutative (pCore 2 A)]
    (S : Sylow 2 G) (hS : A⊓B=(S : Subgroup G)) (hlarge : 8<Nat.card S)
    (hns : ¬ Nonempty (S≃*Multiplicative (ZMod 2)×DihedralGroup 4)) :
    Nonempty (pCore 2 A≃*Multiplicative (ZMod 4)×Multiplicative (ZMod 4)) := by
  have hs := remaining_source_card_thirty_two h hcore hA hB S hS hlarge hns
  have ht : Nat.card (A⊓B : Subgroup G)=32 := hS ▸ hs
  have hq : Nat.card (pCore 2 A)=16 := by have hh := core_half h; omega
  have hz := vertex_center_eq_bot_of_large h hcore hA hB (by omega)
  have hn : ¬ IsElementaryAbelian 2 (pCore 2 A) := by
    intro he
    let := he
    have hh := intersection_card_le_sixteen_of_elementary h hcore hA hB
    omega
  have he : ∃ x : pCore 2 A, x^2≠1 := by
    by_contra! hall
    exact hn { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hall }
  obtain ⟨x,hx⟩ := he
  have hd : orderOf x ∣ 16 := hq ▸ orderOf_dvd_natCard x
  have hn2 : ¬ orderOf x ∣ 2 := by rwa [orderOf_dvd_iff_pow_eq_one]
  have h4 : 4 ∣ orderOf x := by
    have hd' : orderOf x ∣ 2^4 := by norm_num; exact hd
    obtain ⟨n,hn,hxn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd'
    interval_cases n <;> norm_num at hxn <;> rw [hxn] at hn2 ⊢ <;> norm_num at *
  exact NormalSixteenC4Square.recognition_of_commutative _ hz hq
    ⟨x^(orderOf x/4), orderOf_pow_orderOf_div (orderOf_pos x).ne' h4⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.OneAbelian
