module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourParabolic
public import Theory.GroupTheory.NoncentralChiefRefinement.NormalPerfectMovement
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.SpecificGroups.SL2.BinaryDihedral
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.FrattiniQuotient
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# A moved chief section in the original Hermitian mixed two-core

Put P = O₂(I) and J = RH. The original O₂(H) normalizes I and P.
Consequently P is normal in R O₂(H), which is normal in J, so P lies in
O₂(J). The faithful action of I/O₂(I) on P/U then shows that O²(H)
moves O₂(J)/U. Taking the two-residual of its normal closure, and a
maximal proper normal denominator of the resulting commutator, produces
an actual J-chief section above U moved by the original O²(H).

The whole two-core need not be elementary abelian. Chiefness makes the
selected quotient elementary and its binary conjugation representation
irreducible. Thus O₂(J), and hence the full O₂(R), acts trivially; the
original R and O²(H) action images commute. B.6.8(6a) bounds the original
H-kernel by O₂(H) once the earlier nonsolvable sieve has identified the
maximal core. No equality of these kernels or homogeneous natural-module
marking is assumed or asserted.

The companion Chapter 12 application discharges every new input on the
original selected pair. Source: Aschbacher–Smith 8.2.9, printed p.721,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic.Construction Normalizer.SmallOvergroups
open NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

/-- The original pair core lies in the mixed core, by two relative normal steps. -/
theorem selected_one_pair_le_mixed_core
    {V H M I R : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (hTH : (T : Subgroup G) ≤ H)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hHR : H ≤ normalizer (R : Set G))
    (hRP : R ≤ normalizer (I.pCoreIn 2 : Set G))
    (hPH : I.pCoreIn 2 ≤ H.pCoreIn 2) :
    I.pCoreIn 2 ≤ (R ⊔ H).pCoreIn 2 := by
  let D := R ⊔ H.pCoreIn 2
  have hHQ : H ≤ normalizer (H.pCoreIn 2 : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 H).le_sylow_of_normalized T
      (hTH.trans hHQ)
  have hQP : H.pCoreIn 2 ≤ normalizer (I.pCoreIn 2 : Set G) := by
    rw [←s.generate]
    exact Normalizer.normalizes_twoConjugate_core _ V i.val (hQT.trans hTV)
      (hHQ (s.family.le_ambient i.property))
  have hPD : I.pCoreIn 2 ≤ D.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I) (hPH.trans le_sup_right)
      (sup_le hRP hQP)
  have hHD : H ≤ normalizer (D : Set G) :=
    (le_inf hHR hHQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact hPD.trans (pCoreIn_mono_of_normalizes
    (sup_le le_sup_left ((pCoreIn_le 2 H).trans le_sup_right))
    (sup_le (le_sup_left.trans D.le_normalizer) hHD))

private theorem moved_chief_of_twoPerfect_subgroup
    (Z Q : NormalNode G) (D : Subgroup G)
    (hZQ : Z ≤ Q) (hQ : IsPGroup 2 Q.val) (hD : IsPPerfect 2 D)
    (hm : ¬ ⁅Q.val,D⁆ ≤ Z.val) :
    ∃ A B : NormalNode G, Z ≤ A ∧ A ⋖ B ∧ B ≤ Q ∧
      ¬ D ≤ (NoncentralChiefRefinement.sectionAction A B).ker := by
  let N := normalClosure (D : Set G)
  let K := (pResidual 2 N).map N.subtype
  have hDN : D ≤ N := le_normalClosure
  have hp : IsPPerfect 2 (D.subgroupOf N) :=
    hD.of_surjective (subgroupOfEquivOfLe hDN).symm.toMonoidHom
      (subgroupOfEquivOfLe hDN).symm.surjective
  have hDK : D ≤ K := by
    have hh := map_mono (f := N.subtype) (le_pResidual_of_isPPerfect _ hp)
    rwa [map_subgroupOf_eq_of_le hDN] at hh
  let : K.Normal := by dsimp only [K,N]; infer_instance
  obtain ⟨A,B,hZA,hAB,hBQ,hmK⟩ := exists_moved_chief_of_normal_twoPerfect Z Q
    ⟨K,inferInstanceAs K.Normal⟩ hZQ hQ (isPPerfect_embedded_pResidual 2 N)
      (fun hh => hm ((commutator_mono le_rfl hDK).trans hh))
  refine ⟨A,B,hZA,hAB,hBQ,?_⟩
  intro hk
  have hNk : N ≤ (NoncentralChiefRefinement.sectionAction A B).ker :=
    normalClosure_le_normal hk
  have hKk : K ≤ (NoncentralChiefRefinement.sectionAction A B).ker :=
    (map_subtype_le _).trans hNk
  apply hmK
  rw [commutator_comm,commutator_le]
  intro k hkK b hb
  have he := DFunLike.congr_fun (hKk hkK)
    (QuotientGroup.mk' (A.val.subgroupOf B.val) ⟨b,hb⟩)
  rw [NoncentralChiefRefinement.sectionAction_mk] at he
  have hh := QuotientGroup.eq_iff_div_mem.mp he
  change k * b * k⁻¹ / b ∈ A.val at hh
  simpa only [commutatorElement_def,div_eq_mul_inv] using hh



private theorem pair_residual_not_le_core (I : Subgroup G)
    (hpair : Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2)) ∨
      Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5)) :
    ¬ pResidual 2 I ≤ pCore 2 I := by
  intro hc
  have hz : pResidual 2 (I ⧸ pCore 2 I) = ⊥ := by
    rw [←map_pResidual_of_surjective 2 (QuotientGroup.mk' (pCore 2 I))
      (QuotientGroup.mk'_surjective _)]
    exact (Subgroup.map_eq_bot_iff _).mpr (by simpa only [QuotientGroup.ker_mk'] using hc)
  have hp : IsPGroup 2 (I ⧸ pCore 2 I) :=
    (isPGroup_quotient_pResidual 2).of_equiv
      ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot)
  obtain ⟨q,hq,hq2,hcard⟩ : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧
      Nat.card (I ⧸ pCore 2 I) = 2*q := by
    rcases hpair with hpair | hpair
    · obtain ⟨e⟩ := hpair
      refine ⟨3,by decide,by decide,?_⟩
      rw [Nat.card_congr (e.trans
        Theory.SpecificGroups.BinaryDihedral.dihedralThreeEquivPSL2Two.symm).toEquiv,
        DihedralGroup.nat_card]
    · obtain ⟨e⟩ := hpair
      exact ⟨5,by decide,by decide,(Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card⟩
  obtain ⟨m,hm⟩ := hp.exists_card_eq
  have hd : q ∣ 2^m := by rw [←hm,hcard]; exact dvd_mul_left q 2
  exact hq2 ((Nat.dvd_prime Nat.prime_two).mp (hq.dvd_of_dvd_pow hd) |>.resolve_left hq.ne_one)

/-- The faithful original pair makes O²(H) move the actual mixed core modulo U. -/
theorem pair_residual_moves_mixed_core
    {R I V U H : Subgroup G} (hIH : I ≤ H)
    (hp : PairProductAction R I V U)
    (hPQ : I.pCoreIn 2 ≤ (R ⊔ H).pCoreIn 2)
    (hpair : Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2)) ∨
      Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5)) :
    ¬ ⁅(R ⊔ H).pCoreIn 2,(pResidual 2 H).map H.subtype⁆ ≤ U := by
  obtain ⟨hYP,hYU,hUP,_,_,_,_,_,hker,_⟩ := hp
  let := hUP
  intro hc
  apply pair_residual_not_le_core I hpair
  intro a ha
  rw [←hker]
  change inclusion (show I ≤ R ⊔ I from le_sup_right) a ∈
    (Normalizer.SmallOvergroups.sectionAction (R ⊔ I) (I.pCoreIn 2) U hYP hYU).ker
  apply (mem_sectionAction_ker _ _ _ _ _ _).mpr
  intro p
  rw [commutator_comm] at hc
  exact hc (commutator_mem_commutator
    ((embedded_pResidual_mono 2 hIH) (mem_map_of_mem I.subtype ha)) (hPQ p.property))

/-- A chief section of the original mixed two-core, above U, is moved by O²(H).
Its elementary structure, irreducibility and two-core kernel are consequences. -/
theorem selected_one_moved_chief
    {V H M I R U : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (hTH : (T : Subgroup G) ≤ H)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hHR : H ≤ normalizer (R : Set G))
    (hRP : R ≤ normalizer (I.pCoreIn 2 : Set G))
    (hPH : I.pCoreIn 2 ≤ H.pCoreIn 2)
    (hUP : U ≤ I.pCoreIn 2) (hHU : H ≤ normalizer (U : Set G))
    (hp : PairProductAction R I V U)
    (hpair : Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2)) ∨
      Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5)) :
    I.pCoreIn 2 ≤ (R ⊔ H).pCoreIn 2 ∧
    ∃ A B : NormalNode (R ⊔ H : Subgroup G), U.subgroupOf (R ⊔ H) ≤ A.val ∧
      A ⋖ B ∧ B.val ≤ pCore 2 (R ⊔ H : Subgroup G) ∧
      ∃ he : IsElementaryAbelian 2 (Section A B), letI := he
        Representation.IsIrreducible (binarySectionRepresentation A B) ∧
        pCore 2 (R ⊔ H : Subgroup G) ≤ (binarySectionRepresentation A B).ker ∧
        ¬ (((pResidual 2 H).map H.subtype).subgroupOf (R ⊔ H)) ≤
          (NoncentralChiefRefinement.sectionAction A B).ker := by
  let J := R ⊔ H
  have hPQ := selected_one_pair_le_mixed_core s hTH hTV hHR hRP hPH
  have hm := pair_residual_moves_mixed_core s.family.le_ambient hp hPQ hpair
  have hJU : J ≤ normalizer (U : Set G) :=
    sup_le (le_sup_left.trans hp.choose_spec.choose) hHU
  let z : NormalNode J := ⟨U.subgroupOf J,normal_subgroupOf_of_le_normalizer hJU⟩
  let q : NormalNode J := ⟨pCore 2 J,inferInstanceAs (pCore 2 J).Normal⟩
  let D := ((pResidual 2 H).map H.subtype).subgroupOf J
  have hDJ : (pResidual 2 H).map H.subtype ≤ J := (map_subtype_le _).trans le_sup_right
  have hDp : IsPPerfect 2 D := (isPPerfect_embedded_pResidual 2 H).of_surjective
    (subgroupOfEquivOfLe hDJ).symm.toMonoidHom (subgroupOfEquivOfLe hDJ).symm.surjective
  have hzq : z ≤ q := by
    intro u hu
    exact (mem_map_iff_mem J.subtype_injective).mp (hPQ (hUP hu))
  have hmove : ¬ ⁅q.val,D⁆ ≤ z.val := by
    intro hc
    apply hm
    have hh := map_mono (f := J.subtype) hc
    rw [map_commutator,map_subgroupOf_eq_of_le hDJ,
      map_subgroupOf_eq_of_le (hUP.trans ((pCoreIn_le 2 I).trans
        (s.family.le_ambient.trans le_sup_right)))] at hh
    exact hh
  obtain ⟨A,B,hzA,hAB,hBq,ha⟩ := moved_chief_of_twoPerfect_subgroup z q D
    hzq pCore_isPGroup hDp hmove
  let he := chief_elementary A B hAB (pCore_isPGroup.to_le hBq)
  let := he
  let hi := binarySection_irreducible A B hAB
  let := hi
  exact ⟨hPQ,A,B,hzA,hAB,hBq,he,hi,
    normal_p_subgroup_le_ker (binarySectionRepresentation A B) _ pCore_isPGroup,ha⟩



/-- The normal local residual's full two-core is killed on every binary chief
section of RH, so the original O²(H) and R actions commute. -/
theorem mixed_chief_actions_commute
    {R H : Subgroup G} (hHR : H ≤ normalizer (R : Set G))
    (hcomm : ⁅R,(pResidual 2 H).map H.subtype⁆ ≤ R.pCoreIn 2)
    (A B : NormalNode (R ⊔ H : Subgroup G)) (hAB : A ⋖ B)
    (hB : B.val ≤ pCore 2 (R ⊔ H : Subgroup G)) :
    let f := NoncentralChiefRefinement.sectionAction A B
    pCore 2 (R ⊔ H : Subgroup G) ≤ f.ker ∧
    (R.pCoreIn 2).subgroupOf (R ⊔ H) ≤ f.ker ∧
    ∀ (r : R) (a : pResidual 2 H),
      Commute (f (inclusion le_sup_left r)) (f (inclusion le_sup_right a.val)) := by
  let J := R ⊔ H
  let he := chief_elementary A B hAB (pCore_isPGroup.to_le hB)
  let := he
  let := binarySection_irreducible A B hAB
  have hk := normal_p_subgroup_le_ker (binarySectionRepresentation A B) _
    (pCore_isPGroup (p := 2) (G := J))
  let f := NoncentralChiefRefinement.sectionAction A B
  have hkf : pCore 2 J ≤ f.ker := by
    intro a ha
    apply MulEquiv.ext
    intro x
    exact congrArg Additive.toMul (LinearMap.congr_fun (hk ha) (Additive.ofMul x))
  have hRq : R.pCoreIn 2 ≤ J.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le R.le_normalizer hHR)
  have hRk : (R.pCoreIn 2).subgroupOf J ≤ f.ker := by
    intro r hr
    exact hkf ((mem_map_iff_mem J.subtype_injective).mp (hRq hr))
  refine ⟨hkf,hRk,?_⟩
  intro r a
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [←map_commutatorElement]
  apply hRk
  exact hcomm (commutator_mem_commutator r.property (mem_map_of_mem H.subtype a.property))



/-- B.6.8(6a) bounds the kernel on the original H by its full two-core,
using the already identified maximal core and the actual residual movement. -/
theorem hstar_chief_kernel_le
    {H J M V : Subgroup G} {T : Sylow 2 G}
    (hHJ : H ≤ J) (h28 : HypothesisE28 KnownSimple.IsKnownSimple H T M V)
    (hcore : (M.subgroupOf H).normalCore = pCore 2 H)
    (A B : NormalNode J)
    (hm : ¬ (((pResidual 2 H).map H.subtype).subgroupOf J) ≤
      (NoncentralChiefRefinement.sectionAction A B).ker) :
    ((NoncentralChiefRefinement.sectionAction A B).comp (inclusion hHJ)).ker ≤ pCore 2 H := by
  let f := NoncentralChiefRefinement.sectionAction A B
  have hn : ¬ pResidual 2 H ≤ (f.comp (inclusion hHJ)).ker := by
    intro hk
    apply hm
    intro a ha
    obtain ⟨x,hx,he⟩ := ha
    have hea : inclusion hHJ x = a := Subtype.ext he
    rw [←hea]
    exact hk hx
  obtain ⟨t,ht,htP,htM⟩ := h28.minimal
  have hh := ChapterB.minimalParabolic_normal_le_core_of_residual_not_le t htP
    (f.comp (inclusion hHJ)).ker hn
  change (f.comp (inclusion hHJ)).ker ≤ (ChapterB.minimalParabolicMax t htP).normalCore at hh
  rw [←htM,hcore] at hh
  exact hh

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
