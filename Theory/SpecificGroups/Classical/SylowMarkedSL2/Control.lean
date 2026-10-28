module
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.Geometry
public import Theory.GroupTheory.NormalFourThreeDivisor
public import Theory.GroupTheory.CentralizerSmallKernelTransport
/-!
# The marked SL₂(5) subgroup is recovered from its central involution

A Sylow-normalized copy of SL₂(5) contributes its unique involution to the
Sylow center. When that center is cyclic, every Sylow-preserving automorphism
fixes the involution. A bound of 120 on the derived involution centralizer
identifies the original perfect subgroup with that derived subgroup. The
companion model leaves prove these two inputs for the actual classical rows.
Source: the automorphism step of Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Matrix
open scoped MatrixGroups IsMulCommutative
namespace Theory.SpecificGroups.Classical.SylowMarkedSL2
variable {G E : Type*} [Group G] [Finite G] [Field E] [Finite E]
omit [Finite E] in
private theorem sl2_unique_involution (h2 : (2 : E) ≠ 0) (x : SL(2,E))
    (hx : orderOf x = 2) : x = -1 := by
  have hp : x ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
  have hd : (SpecialLinearGroup.toGL x).det = 1 := by apply Units.ext; exact x.property
  rcases GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one h2
    (SpecialLinearGroup.toGL x) (by rw [← map_pow,hp,map_one]) hd with he | he
  · have he' : x = 1 := SpecialLinearGroup.toGL_injective (by simpa using he)
    simp [he'] at hx
  · exact Subtype.ext (congrArg Units.val he)
private theorem exists_sylow_intersection (S : Sylow 2 G) (L : Subgroup G)
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

theorem automorphism_preserves_sl2_five
    (hcyc : ∀ T : Sylow 2 G, ¬ IsMulCommutative T → IsCyclic (center T))
    (hbound : ∀ z : G, orderOf z = 2 → Nat.card (commutator (centralizer ({z} : Set G))) ≤ 120)
    (L : Subgroup G) (eL : L ≃* SL(2,E)) (hE : Nat.card E = 5)
    (S : Sylow 2 G) (hSL : (S : Subgroup G) ≤ normalizer (L : Set G))
    (a : MulAut G) (ha : (S : Subgroup G).map a.toMonoidHom = S) :
    L.map a.toMonoidHom = L := by
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
    exact sl2_unique_involution hE2 (eL x) ((eL.orderOf_eq x).trans hx)
  obtain ⟨P,hP⟩ := exists_sylow_intersection S L hSL
  have hzS : z ∈ S := by
    have hPeven : 2 ∣ Nat.card P := P.dvd_card_of_dvd_card (by rw [hLc]; decide)
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 hPeven
    have he : x.val = zL := huniq x.val ((orderOf_injective (P : Subgroup L).subtype Subtype.val_injective x).trans hx)
    have hxs : x.val ∈ (S : Subgroup G).subgroupOf L := hP ▸ x.property
    change zL.val ∈ S
    rw [← he]
    exact hxs
  have hnS : ¬ IsMulCommutative S := by
    intro hc
    let : IsMulCommutative S := hc
    let P' := P.mapSurjective (f := eL.toMonoidHom) eL.surjective
    apply SpecialLinearGroup.sylow_two_not_isMulCommutative hEodd P'
    let eP : P ≃* P' := (P : Subgroup L).equivMapOfInjective eL.toMonoidHom eL.injective
    apply IsMulCommutative.of_comm
    intro x y
    apply eP.symm.injective
    rw [map_mul,map_mul]
    apply Subtype.ext
    apply L.subtype_injective
    have hin (u : P) : u.val.val ∈ S := by
      have hu : u.val ∈ (S : Subgroup G).subgroupOf L := hP ▸ u.property
      exact hu
    exact congrArg Subtype.val (mul_comm (⟨(eP.symm x).val.val,hin _⟩ : S)
      (⟨(eP.symm y).val.val,hin _⟩ : S))
  let : IsCyclic (center S) := hcyc S hnS
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
  let aS : MulAut S := (a.subgroupMap S).trans (MulEquiv.subgroupCongr ha)
  let aZ := centerCongr aS
  let zz : center S := ⟨⟨z,hzS⟩,hzC⟩
  have hzz : orderOf zz = 2 :=
    (orderOf_injective (center S).subtype Subtype.val_injective zz).symm.trans
      ((orderOf_injective (S : Subgroup G).subtype Subtype.val_injective zz.val).symm.trans hz)
  have haz : a z = z := by
    have he := IsCyclic.eq_of_orderOf_eq_two ((aZ.orderOf_eq zz).trans hzz) hzz
    exact congrArg (fun t : center S => t.val.val) he
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
  have haC : C.map a.toMonoidHom = C := by
    change (centralizer ({z} : Set G)).map a.toMonoidHom = centralizer ({z} : Set G)
    rw [Theory.GroupTheory.CentralizerSmallKernelTransport.map_centralizer a z,haz]
  have hLmap : L.map a.toMonoidHom = L := by
    rw [hLder, map_commutator, haC]
  exact hLmap
end Theory.SpecificGroups.Classical.SylowMarkedSL2
