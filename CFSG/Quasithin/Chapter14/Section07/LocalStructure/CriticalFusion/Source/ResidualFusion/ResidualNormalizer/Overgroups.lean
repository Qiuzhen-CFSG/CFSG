module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Preliminaries
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.Faithfulness
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.FullAction.Components.Selection
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Overgroups.ActionBridge
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import Theory.SpecificGroups.PSL3Two.AlternatingFiveObstruction
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Proper overgroups and the normalizer action in 14.7.67

A proper local overgroup of the residual `K` moves the original point, so
the genuine signalizer-module comparison puts it in the faithful local family.
The earlier implication 14.3.4 then identifies its two-core quotient as A₅ or
L₃(2). We prove the needed small cases of the A.3.14 exclusion directly:
proper subgroups of A₅ are solvable, whereas the order of L₃(2) is prime to five.
In the A₅ case, surjectivity of the image forces the overgroup inside `KT = H`,
where two-perfectness forces it back inside `K`.

The quotient marking `K/O₂(K) ≃ A₅` is induced by the original `qH`, with
relative normality and the kernel made explicit. We also prove
`O∞(K) = O₂(K)`, identifying the radical quotient used in A.3.14.
Conjugation on this same quotient and the actual `S₅ ≃ Aut(A₅)` equivalence
show that `H` realizes every automorphism. Correcting by an element of `H`
leaves the section centralizer `D`, giving `N_G(K) = KDT` both as a subgroup
join and as a literal product of sets.

`EarlierFaithfulClassification` is the genuine universal 14.3.4(1--2)
implication, produced by `qt-14-03`; `Uniqueness127` is produced by
`qt-1-02-adequate-assembly`. Their discharge and the remaining Thompson branch
belong to the parent `qt-14-07-critical-residual-normalizer`. No A.3.14 premise
or additional action-lifting premise is needed here.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemma 14.7.67(3--4), printed pp.1070--1071 (PDF pp.1087--1088), and A.3.14.
-/

@[expose] public section
noncomputable section
open Subgroup Stellmacher Representation
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
open Chapter1.Section02
open Chapter1.Section02.Adequate
open Chapter13.Section06.CentralizerReduction.ComponentSelection
open Chapter14.Section04.LargerDimension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace Data
open ResidualNormalizer
variable (d : Source.Data T L V F W)

/-- The restriction of the original quotient marking to the residual. -/
def qK :
    (K F).subgroupOf F.H →* ChapterJ.S5 :=
  d.qH.comp ((K F).subgroupOf F.H).subtype

def qKA :
    (K F).subgroupOf F.H →* alternatingGroup (Fin 5) where
  toFun k := ⟨qK d k, by
    rw [← K_image d]
    exact mem_map_of_mem d.qH k.property⟩
  map_one' := by ext; simp [qK]
  map_mul' a b := by ext; simp [qK]

/-- The original `qH` has precisely the intrinsic two-core as the kernel on
the residual.  The displayed relative normality is the source normality of
the residual in `H`; it is used to transport the ambient core quotient. -/
theorem qKA_ker :
    (qKA d).ker = pCore 2 ((K F).subgroupOf F.H) := by
  let : ((K F).subgroupOf F.H).Normal :=
    normal_subgroupOf_of_le_normalizer (H_normalizes_K F)
  ext k
  rw [MonoidHom.mem_ker]
  change (qKA d) k = 1 ↔ k ∈ pCore 2 ((K F).subgroupOf F.H)
  rw [Subtype.ext_iff]
  change qK d k = 1 ↔ k ∈ pCore 2 ((K F).subgroupOf F.H)
  change d.qH k = 1 ↔ k ∈ pCore 2 ((K F).subgroupOf F.H)
  rw [← MonoidHom.mem_ker, d.qH_ker]
  have hHcore : (F.H.pCoreIn 2).subgroupOf F.H = pCore 2 F.H := by
    apply map_injective F.H.subtype_injective
    rw [map_subgroupOf_eq_of_le (pCoreIn_le 2 F.H), pCoreIn]
  rw [hHcore]
  rw [pCore_eq_comap_of_normal 2 ((K F).subgroupOf F.H)]
  rfl

theorem qKA_surjective : Function.Surjective (qKA d) := by
  intro a
  have ha : (a : ChapterJ.S5) ∈
      ((K F).subgroupOf F.H).map d.qH := by
    rw [K_image d]
    exact a.property
  obtain ⟨k, hk, he⟩ := mem_map.mp ha
  refine ⟨⟨k, hk⟩, ?_⟩
  exact Subtype.ext he

/-- The quotient `K/O₂(K)` is the actual alternating subgroup in the given
`H/O₂(H) ≃ S₅` marking. -/
noncomputable def K_quotient_equiv_A5 :
    (K F ⧸ pCore 2 (K F)) ≃* alternatingGroup (Fin 5) := by
  let : ((K F).subgroupOf F.H).Normal :=
    normal_subgroupOf_of_le_normalizer (H_normalizes_K F)
  let e₀ := (QuotientGroup.quotientMulEquivOfEq (qKA_ker d).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (qKA d) (qKA_surjective d))
  let e₁ : (K F ⧸ pCore 2 (K F)) ≃*
      ((K F).subgroupOf F.H ⧸ pCore 2 ((K F).subgroupOf F.H)) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe (K_le_H F)).symm
      (pCore_map_iso 2 (subgroupOfEquivOfLe (K_le_H F)).symm)
  exact e₁.trans e₀

/-- Evaluation on the original quotient representatives. -/
theorem K_quotient_equiv_A5_mk (k : K F) :
    (d.K_quotient_equiv_A5 (QuotientGroup.mk' (pCore 2 (K F)) k) : ChapterJ.S5) =
      d.qH ⟨k, K_le_H F k.property⟩ := rfl

private theorem quotient_marking_ker {A B : Type*} [Group A] [Group B]
    (e : (A ⧸ pCore 2 A) ≃* B) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))).ker = pCore 2 A := by
  ext a
  change e (QuotientGroup.mk' _ a) = 1 ↔ a ∈ pCore 2 A
  rw [e.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff _

include d in
/-- The intrinsic radical in the A.3.14 convention is exactly the two-core. -/
theorem K_solvableRadical_eq_pCore : solvableRadical (K F) = pCore 2 (K F) := by
  let f := d.K_quotient_equiv_A5.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (K F)))
  have hf : Function.Surjective f :=
    d.K_quotient_equiv_A5.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 (K F) := quotient_marking_ker _
  let : Group.IsNilpotent f.ker := by
    rw [hk]
    exact (pCore_isPGroup : IsPGroup 2 (pCore 2 (K F))).isNilpotent
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hr : solvableRadical (alternatingGroup (Fin 5)) = ⊥ := by
    rcases (inferInstance : (solvableRadical (alternatingGroup (Fin 5))).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · let : Group.IsSolvable (⊤ : Subgroup (alternatingGroup (Fin 5))) :=
        h ▸ inferInstanceAs (Group.IsSolvable (solvableRadical (alternatingGroup (Fin 5))))
      let : Group.IsSolvable (alternatingGroup (Fin 5)) :=
        Group.isSolvable_of_surjective
          (f := (topEquiv : (⊤ : Subgroup (alternatingGroup (Fin 5))) ≃*
            alternatingGroup (Fin 5)).toMonoidHom) topEquiv.surjective
      exact (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance).elim
  have h := comap_solvableRadical_eq_of_solvable_ker f hf
  rw [hr] at h
  exact h.symm.trans hk

/-- The same actual A₅ marking in the radical-quotient convention. -/
noncomputable def K_radical_quotient_equiv_A5 :
    (K F ⧸ solvableRadical (K F)) ≃* alternatingGroup (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq d.K_solvableRadical_eq_pCore).trans d.K_quotient_equiv_A5

include d in
theorem K_not_solvable : ¬ Group.IsSolvable (K F) := by
  intro hs
  let := hs
  let : Group.IsSolvable (alternatingGroup (Fin 5)) :=
    Group.isSolvable_of_surjective (f := d.K_radical_quotient_equiv_A5.toMonoidHom.comp
      (QuotientGroup.mk' (solvableRadical (K F))))
      (d.K_radical_quotient_equiv_A5.surjective.comp (QuotientGroup.mk'_surjective _))
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance

include d in
/-- Moving the original central involution places every proper overgroup in
the genuine faithful local family. -/
theorem proper_local_overgroup_faithful
    {I : Subgroup G} (hE : IsEvenCharacteristicAt T)
    (hI : I ∈ Chapter1.L G (T : Subgroup G)) (hKI : K F < I) :
    I ∈ MainForward.faithfulLocalComponents T := by
  let M : Subgroup G := I ⊔ (T : Subgroup G)
  have hMH : M ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_, ?_⟩
    · change M.pCoreIn 2 ≠ ⊥
      simpa only [M] using hI.2.2
    · intro x hx
      exact (show (T : Subgroup G) ≤ I ⊔ (T : Subgroup G) from le_sup_right) hx
  have hIM : I ∈ Chapter1.cComponentsIn M := ⟨le_sup_left, hI.1⟩
  have hzT : d.z ∈ (T : Subgroup G) := by
    apply (F.le_seed 1).trans d.natural.chosen.le_sylow
    rw [d.point]
    exact mem_zpowers d.z
  have hzpoint : d.z ∈ F.Vi 1 := by
    rw [d.point]
    exact mem_zpowers d.z
  let _ := d.U_elementary
  let _ : IsElementaryAbelian 2 (F.Vi 1) :=
    IsElementaryAbelian.of_le d.conjugationSection.kernel_le
  have hzsq : d.z ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian d.z hzpoint
  have hcomm : ∀ t ∈ (T : Subgroup G), t * d.z = d.z * t := by
    intro t ht
    exact (mem_centralizer_iff.mp
      (d.H_centralizes_point (F.invariant 1 ht)) d.z hzpoint).symm
  have hzone : d.z ∈ omegaOneCenterAmbient (T : Subgroup G) :=
    (mem_omegaOneCenterAmbient_iff _ _).mpr ⟨hzT, hzsq, hcomm⟩
  have hnc : ¬ I ≤ centralizer ({d.z} : Set G) := by
    intro hIC
    apply d.proper_local_overgroup_moves_point hI hKI
    rw [d.point, zpowers_eq_closure, centralizer_closure]
    exact hIC
  exact faithful_of_moving_cComponent T hE d.z hzone M I hMH hIM hnc

include d in
/-- In the A₅ alternative the image of `K` is all of A₅. The two-core of
the local component lies in `T`, so the overgroup lies in `H` and hence in `K`. -/
theorem K_not_lt_local_with_alternating_quotient {I : Subgroup G}
    (hI : I ∈ Chapter1.L G (T : Subgroup G)) (hKI : K F < I)
    (e : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 5)) : False := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  let f := q.comp (inclusion hKI.le)
  have hk : IsPGroup 2 q.ker := by
    rw [quotient_marking_ker e]
    exact pCore_isPGroup
  have hkf : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.comp (inclusion hKI.le)).ker
    rw [← MonoidHom.comap_ker]
    exact hk.comap_of_injective _ (inclusion_injective hKI.le)
  have hr : f.range = ⊤ := by
    by_contra hn
    let : Group.IsSolvable f.range := alternatingGroup.isSolvable_subgroup_five_of_ne_top _ hn
    let : Group.IsNilpotent f.ker := hkf.isNilpotent
    have hsol : Group.IsSolvable (K F) :=
      Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict (by
        rw [MonoidHom.ker_rangeRestrict, range_subtype])
    exact d.K_not_solvable hsol
  have hs : Function.Surjective f := MonoidHom.range_eq_top.mp hr
  have hIC : I ≤ K F ⊔ I.pCoreIn 2 := by
    intro i hi
    obtain ⟨k, he⟩ := hs (q ⟨i, hi⟩)
    have hx : (inclusion hKI.le k)⁻¹ * (⟨i, hi⟩ : I) ∈ pCore 2 I := by
      rw [← quotient_marking_ker e]
      change q ((inclusion hKI.le k)⁻¹ * (⟨i, hi⟩ : I)) = 1
      rw [map_mul, map_inv, show q (inclusion hKI.le k) = q ⟨i, hi⟩ from he,
        inv_mul_cancel]
    have hm : (k : G)⁻¹ * i ∈ I.pCoreIn 2 := mem_map.mpr ⟨_, hx, rfl⟩
    have hp := (K F ⊔ I.pCoreIn 2).mul_mem (mem_sup_left k.property) (mem_sup_right hm)
    simpa only [mul_inv_cancel_left] using hp
  have hcore : I.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hsub := pCoreAmbient_mono_of_isSubnormalIn I (I ⊔ (T : Subgroup G)) 2
      le_sup_left hI.1.subnormal
    exact hsub.trans ((pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right))
  have hIH : I ≤ F.H := by
    rw [d.residual_product]
    exact hIC.trans (sup_le_sup_left hcore _)
  exact hKI.not_ge (localComponent_le_K_of_le_H hI hIH)

include d in
/-- The actual linear-group carrier has order dividing 168, whereas the
actual A₅ quotient forces five to divide the order of `K`. -/
theorem K_not_lt_local_with_linear_quotient {I : Subgroup G}
    (hKI : K F < I) (e : (I ⧸ pCore 2 I) ≃* Matrix.PSL3Two.PSL) : False := by
  have hfiveK : 5 ∣ Nat.card (K F) := by
    have hcard : Nat.card (K F ⧸ pCore 2 (K F)) = 60 := by
      rw [Nat.card_congr d.K_quotient_equiv_A5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    exact (by decide : 5 ∣ 60).trans (hcard ▸ card_quotient_dvd_card (pCore 2 (K F)))
  have hfiveI := hfiveK.trans (card_dvd_of_le hKI.le)
  obtain ⟨n, hn⟩ := (pCore_isPGroup : IsPGroup 2 (pCore 2 I)).exists_card_eq
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 I), hn,
    Nat.card_congr e.toEquiv] at hfiveI
  rcases Nat.prime_five.dvd_mul.mp hfiveI with h | h
  · exact (by decide : ¬ 5 ∣ 168) (h.trans Matrix.PSL3Two.card_PSL_dvd)
  · exact (by decide : ¬ 5 ∣ 2) (Nat.prime_five.dvd_of_dvd_pow h)

include d in
/-- The maximal-local-component conclusion of 14.7.67(3), conditional only
on the universal earlier faithful classification, 14.3.4(1--2). -/
theorem K_mem_LStar
    (classification : EarlierFaithfulClassification G (T : Subgroup G)) :
    K F ∈ Chapter1.LStar G (T : Subgroup G) := by
  refine ⟨d.K_mem_localFamily, ?_⟩
  intro I hI hKI
  by_cases heq : I = K F
  · exact heq
  have hlt : K F < I := lt_of_le_of_ne hKI (Ne.symm heq)
  have hf := d.proper_local_overgroup_faithful (d.counterexample.qtke.evenCharacteristic T) hI hlt
  have hft := (mem_faithfulLocalComponents_iff T I).mp hf
  rcases (classification I hI hft.2).1 with ha | hl
  · obtain ⟨e⟩ := ha
    exact (d.K_not_lt_local_with_alternating_quotient hI hlt e).elim
  · obtain ⟨e⟩ := hl
    exact (d.K_not_lt_local_with_linear_quotient hlt e).elim

include d in
/-- Apply the genuine 1.2.7 theorem with the maximality just proved. -/
theorem residual_normalizer_unique
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : Uniqueness127 KnownSimple.IsKnownSimple.{u}) :
    Chapter4.UniqueMaximalOvergroup F.H (normalizer (K F : Set G)) :=
  d.residual_normalizer_unique_of_maximal earlier (d.K_mem_LStar classification)

/-- Conjugation on the characteristic two-core quotient of `K`. -/
def residualQuotientAction (F : InvariantFlag T V 3) :
    normalizer (K F : Set G) →* MulAut (K F ⧸ pCore 2 (K F)) :=
  (quotientAut (pCore 2 (K F))).comp (K F).normalizerMonoidHom

/-- Transport of the actual quotient action through the original A₅ marking. -/
def residualAlternatingAction :
    normalizer (K F : Set G) →* MulAut (alternatingGroup (Fin 5)) :=
  (MulAut.congr d.K_quotient_equiv_A5).toMonoidHom.comp (residualQuotientAction F)

/-- The action of `H` is exactly conjugation by its image under the original
`qH`, so its surjectivity realizes all automorphisms of A₅. -/
theorem residualAlternatingAction_on_H (h : F.H) :
    d.residualAlternatingAction ⟨h, H_normalizes_K F h.property⟩ =
      Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv (d.qH h) := by
  apply MulEquiv.ext
  intro a
  obtain ⟨q, rfl⟩ := d.K_quotient_equiv_A5.surjective a
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (K F)) q
  change d.K_quotient_equiv_A5
    (residualQuotientAction F ⟨h, H_normalizes_K F h.property⟩
      (d.K_quotient_equiv_A5.symm (d.K_quotient_equiv_A5 _))) = _
  rw [d.K_quotient_equiv_A5.symm_apply_apply]
  apply Subtype.ext
  rw [show residualQuotientAction F ⟨h, H_normalizes_K F h.property⟩
      (QuotientGroup.mk' (pCore 2 (K F)) k) =
      QuotientGroup.mk' (pCore 2 (K F))
        ((K F).normalizerMonoidHom ⟨h, H_normalizes_K F h.property⟩ k) from
    quotientAut_apply_mk _ _ _, K_quotient_equiv_A5_mk]
  rw [Overgroups.symmetricAutEquiv_apply]
  change d.qH (h * ⟨k, K_le_H F k.property⟩ * h⁻¹) =
    d.qH h * (d.K_quotient_equiv_A5 (QuotientGroup.mk' _ k) : ChapterJ.S5) * (d.qH h)⁻¹
  rw [K_quotient_equiv_A5_mk, map_mul, map_mul, map_inv]

omit [Finite G] in
/-- Trivial quotient action is precisely the commutator bound required for
the ambient section centralizer `D`. -/
theorem residualQuotientAction_ker_le_D :
    (residualQuotientAction F).ker.map (normalizer (K F : Set G)).subtype ≤ D F := by
  apply (Chapter4.le_sectionCentralizer_iff _ _).mpr
  refine ⟨map_subtype_le _, commutator_le.mpr ?_⟩
  intro g hg k hk
  obtain ⟨n, hn, rfl⟩ := mem_map.mp hg
  let x : K F := ⟨k, hk⟩
  let y := (K F).normalizerMonoidHom n x * x⁻¹
  have he := DFunLike.congr_fun (MonoidHom.mem_ker.mp hn)
    (QuotientGroup.mk' (pCore 2 (K F)) x)
  change quotientAut (pCore 2 (K F)) ((K F).normalizerMonoidHom n)
    (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x at he
  rw [quotientAut_apply_mk] at he
  have hy : y ∈ pCore 2 (K F) := by
    apply (QuotientGroup.eq_one_iff y).mp
    change QuotientGroup.mk' (pCore 2 (K F)) y = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  exact mem_map.mpr ⟨y, hy, rfl⟩

include d in
/-- The automorphism correction step in 14.7.67(4), with no extra premise. -/
theorem normalizer_K_eq_sup_D_T :
    normalizer (K F : Set G) = K F ⊔ D F ⊔ (T : Subgroup G) := by
  apply le_antisymm
  · intro g hg
    let n : normalizer (K F : Set G) := ⟨g, hg⟩
    obtain ⟨s, hs⟩ :=
      Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv.surjective
        (d.residualAlternatingAction n)
    obtain ⟨h, hh⟩ := d.qH_surjective s
    let hN : normalizer (K F : Set G) := ⟨h, H_normalizes_K F h.property⟩
    have ha : d.residualAlternatingAction hN = d.residualAlternatingAction n := by
      rw [residualAlternatingAction_on_H, hh, hs]
    have he : residualQuotientAction F (n * hN⁻¹) = 1 := by
      apply (MulAut.congr d.K_quotient_equiv_A5).injective
      change d.residualAlternatingAction (n * hN⁻¹) = (MulAut.congr d.K_quotient_equiv_A5) 1
      rw [map_mul, map_inv, ha, mul_inv_cancel, map_one]
    have hx : g * (h : G)⁻¹ ∈ D F :=
      residualQuotientAction_ker_le_D (mem_map.mpr ⟨n * hN⁻¹, he, rfl⟩)
    have hhH : (h : G) ∈ K F ⊔ (T : Subgroup G) := d.residual_product ▸ h.property
    have hhJ : (h : G) ∈ K F ⊔ D F ⊔ (T : Subgroup G) :=
      (show K F ⊔ (T : Subgroup G) ≤ K F ⊔ D F ⊔ (T : Subgroup G) from
        sup_le (le_sup_left.trans le_sup_left) le_sup_right) hhH
    have hxJ : g * (h : G)⁻¹ ∈ K F ⊔ D F ⊔ (T : Subgroup G) :=
      (show D F ≤ K F ⊔ D F ⊔ (T : Subgroup G) from le_sup_right.trans le_sup_left) hx
    simpa only [inv_mul_cancel_right] using
      (K F ⊔ D F ⊔ (T : Subgroup G)).mul_mem hxJ hhJ
  · exact sup_le (sup_le (K F).le_normalizer D_le_normalizer)
      ((F.invariant 1).trans (H_normalizes_K F))

include d in
/-- The source product `KDT` is a literal product: `D` normalizes `K`, and
`T` normalizes both `K` and `D`. -/
theorem normalizer_K_eq_product_D_T :
    (normalizer (K F : Set G) : Set G) =
      (K F : Set G) * (D F : Set G) * (T : Set G) := by
  have hTKD : (T : Subgroup G) ≤ normalizer ((K F ⊔ D F : Subgroup G) : Set G) := by
    apply (le_inf ((F.invariant 1).trans (H_normalizes_K F))
      (((F.invariant 1).trans (H_normalizes_K F)).trans normalizer_K_normalizes_D)).trans
    exact normalizer_inf_normalizer_le_normalizer_sup _ _
  rw [d.normalizer_K_eq_sup_D_T,
    coe_mul_of_right_le_normalizer_left _ _ hTKD,
    coe_mul_of_right_le_normalizer_left _ _ D_le_normalizer, Sylow.coe_coe]

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
