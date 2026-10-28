module
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.Control
public import Theory.GroupTheory.SemidihedralCenter
public import Theory.GroupTheory.NormalFourThreeDivisor
public import Theory.GroupTheory.CentralizerSmallKernelTransport
/-!
# A fixed semidihedral central involution recovers the marked SL₂(5)

The unique involution of a Sylow-normalized SL₂(5) lies in the Sylow center.
For the explicit semidihedral group of order sixteen this is the fourth
power of the order-eight generator. A derived-centralizer bound of 120
recovers the original SL₂(5), so fixing that involution suffices for
normalization, with no invariant-Sylow hypothesis on the automorphism.

Source: Aschbacher--Smith, Proposition 9.3.1, printed p.732, using the
unitary embedding of A.3.14; compare C.5.12, printed p.163.
-/
public section
open Subgroup Matrix
open scoped MatrixGroups IsMulCommutative
namespace Theory.SpecificGroups.Classical.SylowMarkedSL2
variable {G E : Type*} [Group G] [Finite G] [Field E] [Finite E]
omit [Finite E] in
private theorem sl2_unique_involution_fourth (h2 : (2 : E) ≠ 0) (x : SL(2,E))
    (hx : orderOf x = 2) : x = -1 := by
  have hp : x ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
  have hd : (SpecialLinearGroup.toGL x).det = 1 := by apply Units.ext; exact x.property
  rcases GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one h2
    (SpecialLinearGroup.toGL x) (by rw [← map_pow,hp,map_one]) hd with he | he
  · have he' : x = 1 := SpecialLinearGroup.toGL_injective (by simpa using he)
    simp [he'] at hx
  · exact Subtype.ext (congrArg Units.val he)
private theorem exists_sylow_intersection_fourth (S : Sylow 2 G) (L : Subgroup G)
    (hSL : (S : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ P : Sylow 2 L, (P : Subgroup L) = (S : Subgroup G).subgroupOf L := by
  let W := L ⊔ (S : Subgroup G)
  have hLW : L ≤ W := le_sup_left
  let : (L.subgroupOf W).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLW).mpr (sup_le L.le_normalizer hSL)
  obtain ⟨P,hP⟩ := (S.subtype (show (S : Subgroup G) ≤ W from le_sup_right)).exists_subgroupOf_eq_of_normal (L.subgroupOf W)
  let e := subgroupOfEquivOfLe hLW
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change (P : Subgroup _).map e.toMonoidHom = _
  rw [hP]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩; exact hy
  · intro hx; exact ⟨⟨⟨x,hLW x.property⟩,x.property⟩,hx,rfl⟩

theorem automorphism_preserves_sl2_five_of_fix_fourth
    (hbound : ∀ z : G, orderOf z = 2 → Nat.card (commutator (centralizer ({z} : Set G))) ≤ 120)
    (L : Subgroup G) (eL : L ≃* SL(2,E)) (hE : Nat.card E = 5)
    (S : Sylow 2 G) (hSL : (S : Subgroup G) ≤ normalizer (L : Set G))
    (a b : S) (ha : orderOf a = 8) (hb : orderOf b = 2)
    (hab : b*a*b⁻¹=a^3) (hgen : closure ({a,b} : Set S)=⊤)
    (c : MulAut G) (hc : c ((a : G)^4)=(a : G)^4) :
    L.map c.toMonoidHom = L := by
  classical
  have hEodd : Odd (Nat.card E) := by rw [hE]; decide
  have hE2 : (2 : E) ≠ 0 := GorensteinWalter.two_ne_zero_of_odd_card E hEodd
  let : Group.IsPerfect SL(2,E) := GorensteinWalter.sl2_isPerfect_of_card_gt_three E (by omega)
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  have hLc : Nat.card L = 120 := by
    rw [Nat.card_congr eL.toEquiv,GorensteinWalter.sl2_card_formula,hE]
    norm_num
  let zL := eL.symm (-1)
  let z : G := zL.val
  have hzL : orderOf zL = 2 := (eL.symm.orderOf_eq _).trans
    (SpecialLinearGroup.orderOf_neg_one_eq_two hE2)
  have hz : orderOf z = 2 := (orderOf_injective L.subtype L.subtype_injective zL).trans hzL
  have huniq (x : L) (hx : orderOf x = 2) : x = zL := by
    apply eL.injective
    rw [eL.apply_symm_apply]
    exact sl2_unique_involution_fourth hE2 (eL x) ((eL.orderOf_eq x).trans hx)
  obtain ⟨P,hP⟩ := exists_sylow_intersection_fourth S L hSL
  have hzS : z ∈ S := by
    have hPeven : 2 ∣ Nat.card P := P.dvd_card_of_dvd_card (by rw [hLc]; decide)
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 hPeven
    have he : x.val = zL := huniq x.val ((orderOf_injective (P : Subgroup L).subtype Subtype.val_injective x).trans hx)
    have hxs : x.val ∈ (S : Subgroup G).subgroupOf L := hP ▸ x.property
    change zL.val ∈ S
    rw [← he]
    exact hxs
  have hzC : (⟨z,hzS⟩ : S) ∈ center S := by
    apply mem_center_iff.mpr
    intro s
    have hzsL : s.val * z * s.val⁻¹ ∈ L := (mem_normalizer_iff.mp (hSL s.property) z).mp zL.property
    have hzs : orderOf (⟨s.val*z*s.val⁻¹,hzsL⟩ : L) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact ((MulAut.conj s.val).orderOf_eq z).trans hz
    have he := congrArg Subtype.val (huniq ⟨_,hzsL⟩ hzs)
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mp he
  have hcenter : center S = zpowers (a^4) := by
    simpa using Semidihedral.center_eq (G := (S : Subgroup G)) (n := 4) (by decide) a b ha hb hab hgen
  have ha4 : orderOf (a^4) = 2 := by rw [orderOf_pow,ha]; norm_num
  have hza : (⟨z,hzS⟩ : S)=a^4 := by
    rw [hcenter,mem_zpowers_iff_mem_range_orderOf,ha4] at hzC
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hzC
    have hi2 : i<2 := Finset.mem_range.mp hi
    have hi' : i=0 ∨ i=1 := by omega
    rcases hi' with rfl | rfl
    · have hz1 : z=1 := congrArg Subtype.val (by simpa using he.symm : (⟨z,hzS⟩ : S)=1)
      simp [hz1] at hz
    · simpa using he.symm
  have haz : c z=z := by
    have he : z=(a:G)^4 := congrArg Subtype.val hza
    simpa only [he] using hc
  let C := centralizer ({z} : Set G)
  have hLC : L ≤ C := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    have he : (⟨x,hx⟩ : L) * zL = zL * ⟨x,hx⟩ := by
      apply eL.injective
      simp only [map_mul,show eL zL = -1 from eL.apply_symm_apply _]
      simp
    exact congrArg Subtype.val he
  have hLder : L = ⁅C,C⁆ := by
    apply eq_of_le_of_card_ge
    · rw [← L.commutator_eq_self]
      exact commutator_mono hLC hLC
    · have hc := hbound z hz
      rw [← map_subtype_commutator,card_map_of_injective C.subtype_injective]
      exact hc.trans_eq hLc.symm
  have haC : C.map c.toMonoidHom = C := by
    change (centralizer ({z} : Set G)).map c.toMonoidHom = centralizer ({z} : Set G)
    rw [Theory.GroupTheory.CentralizerSmallKernelTransport.map_centralizer c z,haz]
  have hLmap : L.map c.toMonoidHom = L := by
    rw [hLder, map_commutator, haC]
  exact hLmap
end Theory.SpecificGroups.Classical.SylowMarkedSL2
