module
public import Theory.GroupTheory.WreathedTwoFiveCenter
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.SignedThree
public import Theory.SpecificGroups.GL2.FiveWreathSylow
public import Theory.GroupTheory.SingleInvolutionClassSylow

/-!
# A wreathed intersection preserves its marked SL₂(5)

A Sylow-normalized SL₂(5) has a unique involution in the cyclic Sylow
center. A subgroup of order dividing 2^k·5 containing the whole wreathed
Sylow makes that involution characteristic. Its automorphism stabilizer
therefore preserves the original SL₂(5), recovered as the derived involution
centralizer of order 120. No preservation of the chosen Sylow is assumed.

The actual PSL₃(5) model has wreathed Sylow two-subgroups: compare the
odd-index involution centralizer with GL₂(5), then retain the odd central
kernel in the projective quotient.

Source: Aschbacher–Smith C.5.12 and5.1.13, pp.163,637–638; the source
5.2.2 application is in RankOneModuleGenericExceptionalCartanGlobalPrimeLinearFive.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace Theory.SpecificGroups.Classical.SylowMarkedSL2
open Matrix
variable {G E : Type*} [Group G] [Finite G] [Field E] [Finite E]
omit [Finite E] in
private theorem sl2_unique_involution_wreathed (h2 : (2 : E) ≠ 0) (x : SL(2,E))
    (hx : orderOf x = 2) : x = -1 := by
  have hp : x ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
  have hd : (SpecialLinearGroup.toGL x).det = 1 := by apply Units.ext; exact x.property
  rcases GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one h2
    (SpecialLinearGroup.toGL x) (by rw [← map_pow,hp,map_one]) hd with he | he
  · have he' : x = 1 := SpecialLinearGroup.toGL_injective (by simpa using he)
    simp [he'] at hx
  · exact Subtype.ext (congrArg Units.val he)
private theorem exists_sylow_intersection_wreathed (S : Sylow 2 G) (L : Subgroup G)
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

/-- Preserving the actual two-five intersection preserves its Sylow-marked SL₂(5). -/
theorem automorphism_preserves_sl2_five_of_wreathed_intersection
    (hW : ∀ S : Sylow 2 G, Nonempty (S ≃* WreathedThirtyTwo))
    (hbound : ∀ z : G, orderOf z = 2 → Nat.card (commutator (centralizer ({z} : Set G))) ≤ 120)
    (L J : Subgroup G) (eL : L ≃* SL(2,E)) (hE : Nat.card E = 5)
    (S : Sylow 2 G) (hSL : (S : Subgroup G) ≤ normalizer (L : Set G))
    (hSJ : (S : Subgroup G) ≤ J) {k : ℕ} (hd : Nat.card J ∣ 2^k*5)
    (a : MulAut G) (hJ : J.map a.toMonoidHom = J) :
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
    exact sl2_unique_involution_wreathed hE2 (eL x) ((eL.orderOf_eq x).trans hx)
  obtain ⟨P,hP⟩ := exists_sylow_intersection_wreathed S L hSL
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
  let Q := S.subtype hSJ
  let eQ : Q ≃* S := subgroupOfEquivOfLe hSJ
  let zQ : Q := eQ.symm ⟨z,hzS⟩
  have hzQ : orderOf zQ = 2 := (eQ.symm.orderOf_eq _).trans ((orderOf_coe _).symm.trans hz)
  have hzQc : zQ ∈ center Q := (centerCongr eQ.symm ⟨⟨z,hzS⟩,hzC⟩).property
  let ψ : MulAut J := (J.equivMapOfInjective a.toMonoidHom a.injective).trans
    (MulEquiv.subgroupCongr hJ)
  have hh := Theory.GroupTheory.WreathedTwoFive.fixed_central_involution Q (eQ.trans (hW S).some) hd zQ hzQ hzQc ψ
  have haz : a z = z := congrArg J.subtype hh
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

namespace Theory.SpecificGroups.Classical.SylowMarkedSL2
open Matrix
open scoped MatrixGroups
variable {F : Type*} [Field F] [Finite F]
/-- The actual Sylow two-subgroups of PSL₃(5) have the wreathed model. -/
theorem psl3_five_sylow_wreath (hF : Nat.card F = 5) (T : Sylow 2 PSL(3,F)) :
    Nonempty (T ≃* WreathedThirtyTwo) := by
  let : Fintype F := Fintype.ofFinite F
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let eF : F ≃+* ZMod 5 := FiniteField.ringEquivOfCardEq (show Fintype.card F = Fintype.card (ZMod 5) from by
    simpa only [Nat.card_eq_fintype_card,ZMod.card] using hF)
  let eGL : GL (Fin 2) F ≃* GL (Fin 2) (ZMod 5) := Units.mapEquiv eF.mapMatrix.toMulEquiv
  let P : Sylow 2 (GL (Fin 2) F) := Classical.choice inferInstance
  let eP : P ≃* WreathedThirtyTwo := (eGL.subgroupMap P).trans
    (GeneralLinearGroup.FiveWreathSylow.sylowWreathEquiv (P.mapSurjective eGL.surjective))
  let S : Sylow 2 SL(3,F) := Classical.choice inferInstance
  have h2 : (2:F) ≠ 0 := GorensteinWalter.two_ne_zero_of_odd_card F (by rw [hF]; decide)
  have hi := odd_index_centralizer_of_one_involution_class
    (SL3.standardInvolution F) (SL3.standardInvolution_orderOf F h2)
    (fun z hz => SL3.involution_isConj_standard F z hz h2)
  obtain ⟨e⟩ := sylow_equiv_of_odd_index _ hi
    (SL3.standardInvolutionCentralizerEquiv F h2).symm S P
  have hk : Nat.Coprime 2 (Nat.card (PSL3.projection F).ker) := by
    rw [PSL3.projection_ker]
    exact (SL3.odd_card_center F).coprime_two_left
  let eT := Sylow.equivOfSurjectiveCoprime (PSL3.projection F) (PSL3.projection_surjective F) hk S T
  exact ⟨eT.symm.trans (e.trans eP)⟩

end Theory.SpecificGroups.Classical.SylowMarkedSL2
