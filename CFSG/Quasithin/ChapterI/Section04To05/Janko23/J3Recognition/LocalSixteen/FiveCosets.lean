module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.PlaneSplitting
public import Theory.GroupTheory.ElementarySixteenNineNormalizer
public import Theory.ElementaryAbelian.EightQuotientRank
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The actual five-coset action and its central cubic kernel

Let N be the full normalizer of an elementary plane A, B its common
stabilizer with R, and J the normal core of B in N. The root group is a
normal Sylow two-subgroup of B. Since O₂(N)=A, relative normality forces
R ∩ J=A, so the image of J in Aut(A) has order dividing nine. Its order
cannot be one, by the faithful five-coset bound, or nine, by the proved
normalizer theorem for a nine-group on an elementary sixteen-group and
the order-five element in the full automizer. Thus |J|=48, and the literal
five-coset image is A₅.

The image of J in the automizer has order three. Its conjugation action
factors through the perfect A₅ quotient and lands in the abelian
automorphism group of a cubic, so it is central. All subgroups and maps
are formed in the original ambient normalizer.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 46.14(5a), p.258.
This proves the stated permutation-image and kernel step. Natural F₄
coordinates and the GL₂(4) action marking are subsequent obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.HyperbolicRecognition
open scoped IsMulCommutative
namespace CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen
open Matrix.PSL3Four
variable {G : Type*} [Group G] [Finite G] {D : Seed G}
namespace ReturningPair
variable (P : ReturningPair D)

private theorem no_normal_nine_in_plane_automizer (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R)
    (L : Subgroup (MulAut A))
    (hL : A.normalizerMonoidHom.range ≤ normalizer (L : Set (MulAut A))) :
    Nat.card L ≠ 9 := by
  intro h9
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := A.normalizerMonoidHom.range) 5
    (by rw [P.plane_normalizer_action_card hclass A hA hAR]; decide)
  let y : normalizer (L : Set (MulAut A)) := ⟨x,hL x.property⟩
  have hy : orderOf y = 5 := (Subgroup.orderOf_coe y).symm.trans ((Subgroup.orderOf_coe x).trans hx)
  have hm : (y : MulAut A) ∈ L := by
    have hm := mem_map_of_mem (normalizer (L : Set (MulAut A))).subtype
      (mem_pResidual_of_orderOf_coprime (p := 2) (by rw [hy]; decide))
    exact (normalizer_residual_of_elementary_sixteen_nine hA L h9).le hm
  have hd := L.orderOf_dvd_natCard hm
  rw [Subgroup.orderOf_coe,hy,h9] at hd
  norm_num at hd

/-- The five-coset kernel acts on the plane through a group of order three. -/
theorem plane_five_coset_kernel_action_card (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    Nat.card (((normalizer (P.R : Set G)).subgroupOf (normalizer (A : Set G))).normalCore.map
      A.normalizerMonoidHom) = 3 := by
  let N := normalizer (A : Set G)
  let V := A.subgroupOf N
  let U := P.R.subgroupOf N
  let B := (normalizer (P.R : Set G)).subgroupOf N
  let J := B.normalCore
  let L := J.map A.normalizerMonoidHom
  have hRN := P.R_le_plane_normalizer A hA hAR
  have hV : Nat.card V = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show A ≤ N from le_normalizer)).toEquiv).trans hA
  have hU : Nat.card U = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe hRN).toEquiv).trans P.R_card
  have hB : Nat.card B = 576 := by
    dsimp only [B]
    rw [←inf_subgroupOf_right,Nat.card_congr (subgroupOfEquivOfLe
      (show normalizer (P.R : Set G) ⊓ N ≤ N from inf_le_right)).toEquiv,inf_comm]
    exact P.plane_root_stabilizer_card A hA hAR
  have hBi : B.index = 5 := P.root_stabilizer_index_in_plane_normalizer hclass A hA hAR
  have hN : Nat.card N = 2880 := P.plane_normalizer_card hclass A hA hAR
  have hker : A.normalizerMonoidHom.ker = V := P.plane_normalizer_action_kernel A hA hAR
  have hVU : V ≤ U := fun _ hx => hAR hx
  have hUB : U ≤ B := fun _ hx => le_normalizer hx
  have hVJ : V ≤ J := normal_le_normalCore.mpr (hVU.trans hUB)
  have hBU : B ≤ normalizer (U : Set N) := by
    intro b hb
    apply mem_normalizer_iff.mpr
    intro u
    exact mem_normalizer_iff.mp hb (u : G)
  have hUJ : U ⊓ J = V := by
    apply le_antisymm
    · let S := U.subgroupOf J
      let : S.Normal := normal_subgroupOf_of_le_normalizer (B.normalCore_le.trans hBU)
      have hp : IsPGroup 2 S := P.R_isPGroup.comap_subtype.comap_subtype
      have hS : S ≤ pCore 2 J := le_sSup ⟨inferInstance,hp⟩
      have hcore : (pCore 2 J).map J.subtype ≤ pCore 2 N :=
        le_sSup ⟨inferInstance,pCore_isPGroup.map J.subtype⟩
      rw [P.plane_normalizer_twoCore hclass A hA hAR] at hcore
      intro n hn
      exact hcore (mem_map_of_mem J.subtype (hS (show (⟨n,hn.2⟩ : J) ∈ S from hn.1)))
    · exact le_inf hVU hVJ
  let : (U.subgroupOf B).Normal := normal_subgroupOf_of_le_normalizer hBU
  have hUi : U.relIndex B = 9 := by
    have hh := (U.subgroupOf B).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hUB).toEquiv,hU,hB] at hh
    change 64 * U.relIndex B = 576 at hh
    omega
  have hd : U.relIndex J ∣ 9 := by
    have hh := (U.subgroupOf B).relIndex_dvd_index_of_normal (J.subgroupOf B)
    rw [relIndex_subgroupOf B.normalCore_le] at hh
    exact hUi ▸ hh
  have hjc : Nat.card J = 16 * U.relIndex J := by
    have hh := (U.subgroupOf J).card_mul_index
    have hc : Nat.card (U.subgroupOf J) = 16 := by
      rw [←inf_subgroupOf_right,Nat.card_congr (subgroupOfEquivOfLe
        (show U ⊓ J ≤ J from inf_le_right)).toEquiv,hUJ,hV]
    rw [hc] at hh
    exact hh.symm
  have hmap : 16 * Nat.card L = Nat.card J := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map J A.normalizerMonoidHom
    rw [hker,inf_eq_right.mpr hVJ,hV] at hh
    exact hh
  have hLd : Nat.card L ∣ 9 := by
    have he : Nat.card L = U.relIndex J := by omega
    exact he ▸ hd
  have hLp : Nat.card L = 1 ∨ Nat.card L = 3 ∨ Nat.card L = 9 := by
    have hb := Nat.le_of_dvd (by decide : 0 < 9) hLd
    interval_cases hh : Nat.card L <;> norm_num at *
  have hnot9 : Nat.card L ≠ 9 := P.no_normal_nine_in_plane_automizer hclass A hA hAR L (by
    rintro _ ⟨n,rfl⟩
    exact J.le_normalizer_map A.normalizerMonoidHom (mem_map_of_mem _ (le_normalizer_of_normal (mem_top n))))
  have hnot1 : Nat.card L ≠ 1 := by
    intro h1
    have hj : Nat.card J = 16 := by rw [h1] at hmap; omega
    have hi : J.index = 180 := by
      have hh := J.card_mul_index
      rw [hj,hN] at hh
      omega
    have hh : J.index ∣ B.index.factorial := by
      change B.normalCore.index ∣ B.index.factorial
      rw [normalCore_eq_ker,index_ker,index_eq_card,←Nat.card_perm]
      exact card_subgroup_dvd_card (MulAction.toPermHom N (N ⧸ B)).range
    rw [hi,hBi] at hh
    norm_num [Nat.factorial] at hh
  exact hLp.resolve_left hnot1 |>.resolve_right hnot9

/-- The kernel of the original five-coset action has order 48. -/
theorem plane_five_coset_kernel_card (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    Nat.card (((normalizer (P.R : Set G)).subgroupOf (normalizer (A : Set G))).normalCore) = 48 := by
  let N := normalizer (A : Set G)
  let V := A.subgroupOf N
  let J := ((normalizer (P.R : Set G)).subgroupOf N).normalCore
  have hVJ : V ≤ J := normal_le_normalCore.mpr (fun _ hx => le_normalizer (hAR hx))
  have hV : Nat.card V = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show A ≤ N from le_normalizer)).toEquiv).trans hA
  have hh := IsElementaryAbelian.card_inf_ker_mul_card_map J A.normalizerMonoidHom
  rw [P.plane_normalizer_action_kernel A hA hAR,inf_eq_right.mpr hVJ,hV,
    P.plane_five_coset_kernel_action_card hclass A hA hAR] at hh
  exact hh.symm

/-- On its literal five cosets the whole normalizer induces exactly A₅. -/
theorem plane_five_coset_action (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    ∃ e : ((normalizer (A : Set G)) ⧸
        (normalizer (P.R : Set G)).subgroupOf (normalizer (A : Set G))) ≃ Fin 5,
      ((Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom
        (normalizer (A : Set G)) ((normalizer (A : Set G)) ⧸
          (normalizer (P.R : Set G)).subgroupOf (normalizer (A : Set G))))).range =
        alternatingGroup (Fin 5) := by
  let N := normalizer (A : Set G)
  let B := (normalizer (P.R : Set G)).subgroupOf N
  have hfive : Nat.card (N ⧸ B) = 5 := P.root_stabilizer_index_in_plane_normalizer hclass A hA hAR
  let e : (N ⧸ B) ≃ Fin 5 := (Finite.equivFin (N ⧸ B)).trans (Equiv.cast (congrArg Fin hfive))
  let f := (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom N (N ⧸ B))
  have hk : f.ker = B.normalCore := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ (Equiv.permCongrHom e).injective]
    exact B.normalCore_eq_ker.symm
  have hr : Nat.card f.range = 60 := by
    have hh := f.ker.card_mul_index
    rw [index_ker,hk,P.plane_five_coset_kernel_card hclass A hA hAR,
      P.plane_normalizer_card hclass A hA hAR] at hh
    omega
  have hi : f.range.index = 2 := by
    have hh := f.range.card_mul_index
    rw [hr,Nat.card_perm,Nat.card_fin] at hh
    norm_num [Nat.factorial] at hh
    omega
  exact ⟨e,Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi⟩

/-- The literal five-coset kernel, with an actual alternating quotient. -/
theorem plane_five_coset_quotient (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    Nonempty (((normalizer (A : Set G)) ⧸
      ((normalizer (P.R : Set G)).subgroupOf (normalizer (A : Set G))).normalCore) ≃*
        alternatingGroup (Fin 5)) := by
  obtain ⟨e,he⟩ := P.plane_five_coset_action hclass A hA hAR
  let N := normalizer (A : Set G)
  let B := (normalizer (P.R : Set G)).subgroupOf N
  let f := (Equiv.permCongrHom e).toMonoidHom.comp (MulAction.toPermHom N (N ⧸ B))
  have hk : B.normalCore = f.ker := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ (Equiv.permCongrHom e).injective]
    exact B.normalCore_eq_ker
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr he))⟩

/-- The image of the original five-coset kernel is a central cubic subgroup of the automizer. -/
theorem plane_automizer_central_cubic (hclass : OneInvolutionClass G)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) (hAR : A ≤ P.R) :
    let C := (((normalizer (P.R : Set G)).subgroupOf (normalizer (A : Set G))).normalCore).map
      A.normalizerMonoidHom.rangeRestrict
    Nat.card C = 3 ∧ C ≤ center A.normalizerMonoidHom.range := by
  let N := normalizer (A : Set G)
  let H := A.normalizerMonoidHom.range
  let J := ((normalizer (P.R : Set G)).subgroupOf N).normalCore
  let a : N →* H := A.normalizerMonoidHom.rangeRestrict
  let C := J.map a
  have hC : Nat.card C = 3 := by
    rw [←card_map_of_injective H.subtype_injective (K := C),Subgroup.map_map]
    exact P.plane_five_coset_kernel_action_card hclass A hA hAR
  let : C.Normal := (inferInstance : J.Normal).map a A.normalizerMonoidHom.rangeRestrict_surjective
  let : IsCyclic C := isCyclic_of_prime_card hC
  let : IsCyclic (MulAut C) := isCyclic_of_prime_card (p := 2) (by
    rw [IsCyclic.card_mulAut,hC]
    decide)
  let t : H →* MulAut C := MulAut.conjNormal
  have hJ : J ≤ (t.comp a).ker := by
    intro n hn
    change MulAut.conjNormal (a n) = (1 : MulAut C)
    have han : a n ∈ C := mem_map_of_mem a hn
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    change a n * (c : H) * (a n)⁻¹ = c
    have hh := congrArg Subtype.val (mul_comm (⟨a n,han⟩ : C) c)
    exact mul_inv_eq_iff_eq_mul.mpr hh
  let q : (N ⧸ J) →* MulAut C := QuotientGroup.lift J (t.comp a) hJ
  obtain ⟨e⟩ := P.plane_five_coset_quotient hclass A hA hAR
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (N ⧸ J) := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsPerfect q.range := Group.IsPerfect.range q
  have hq (x : N ⧸ J) : q x = 1 := congrArg Subtype.val
    (Subsingleton.elim (⟨q x,⟨x,rfl⟩⟩ : q.range) 1)
  refine ⟨hC,?_⟩
  intro c hc
  apply mem_center_iff.mpr
  intro b
  obtain ⟨n,rfl⟩ := A.normalizerMonoidHom.rangeRestrict_surjective b
  have ht : t (a n) = 1 := hq (QuotientGroup.mk n)
  have hh := congrArg (fun t : MulAut C => (t ⟨c,hc⟩ : H)) ht
  exact mul_inv_eq_iff_eq_mul.mp hh

end ReturningPair
end CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen
