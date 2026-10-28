module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.CanonicalGeometry.Source
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Radical Sylow geometry and faithful canonical supplements in 13.1.9

For T-invariant L, the literal R=C_T(L/O∞(L)) is T∩O∞(LT):
O∞(L)R is solvable and normal in LT, and [L,O∞(LT)] lies in O∞(L).
Sylow restriction discharges the premise of the canonical Frattini theorem.
This supplies Y=N_L(R)^∞, all residual products and O₂(YT)=R.

The actual moved module U=[R₂(N_G(L)),L] is still fully moved by Y.
Its commuting R-action and U≤R force Y to move C_U(R)≤Ω₁Z(R).
A.4.8 then proves Y belongs to the faithful local family, without reversing
A.4.10(3). The later comparison and PSL₂(p) two-core model are proved
conditional on the source intersection O∞(LT)∩YT=R.

The original full Fitting Frattini action and radical quotient image are
specified below for the remaining inversion and intersection proofs.
Cyclicity, the omega inverter and that intersection are not asserted here.
All homocyclic exponents and all primes are retained in the section.

Source: Aschbacher--Smith, 13.1.8--9, printed p.869, and A.4.8, p.60.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter1
variable {G : Type*} [Group G]

/-- The actual image of R in the local two-core quotient. -/
def radicalTwoCoreImage (T L : Subgroup G) : Subgroup (XiQuotient (L ⊔ T)) :=
  ((radicalSylowCentralizer T L).subgroupOf (L ⊔ T)).map
    (QuotientGroup.mk' (pCore 2 (L ⊔ T : Subgroup G)))

/-- The full mixed-prime Fitting Frattini section of the original quotient. -/
abbrev LocalFittingSection (L : Subgroup G) :=
  fittingSubgroup (XiQuotient L) ⧸ frattini (fittingSubgroup (XiQuotient L))

/-- The normalizer's original conjugation action on the full section. -/
def localFittingSectionAction (L : Subgroup G) :
    normalizer (L : Set G) →* MulAut (LocalFittingSection L) :=
  (quotientAut (frattini (fittingSubgroup (XiQuotient L)))).comp
    ((MulAut.characteristic (fittingSubgroup (XiQuotient L))).comp
      ((quotientAut (pCore 2 L)).comp L.normalizerMonoidHom))

/-- The exact inversion assertion needed to eliminate the canonical odd
radical. The element belongs to the original R, and acts by its original
ambient conjugation. Its quotient order and omega identification are
separate assertions in the source construction. -/
def HasRadicalInverter (T L : Subgroup G) : Prop :=
  ∃ r : normalizer (L : Set G), (r : G) ∈ radicalSylowCentralizer T L ∧
    ∀ x : LocalFittingSection L, localFittingSectionAction L r x = x⁻¹

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter1 Chapter1.Section02 Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem solvable_normal_in_le_radical {A B : Subgroup G}
    [Group.IsSolvable A] (hAB : A ≤ B) (hn : B ≤ normalizer (A : Set G)) :
    A ≤ (solvableRadical B).map B.subtype := by
  let : (A.subgroupOf B).Normal := normal_subgroupOf_of_le_normalizer hn
  let e := subgroupOfEquivOfLe hAB
  let : Group.IsSolvable (A.subgroupOf B) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hm := map_mono (f := B.subtype)
    (le_solvableRadical (A.subgroupOf B) inferInstance inferInstance)
  rwa [map_subgroupOf_eq_of_le hAB] at hm

/-- The literal section centralizer is the intersection with the radical
of LT. Only T-invariance of L is needed. -/
theorem radicalSylowCentralizer_eq_inf_radical (T : Sylow 2 G) {L : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    radicalSylowCentralizer T L = (T : Subgroup G) ⊓
      (solvableRadical (L ⊔ (T : Subgroup G) : Subgroup G)).map
        (L ⊔ (T : Subgroup G)).subtype := by
  let W := L ⊔ (T : Subgroup G)
  let D := (solvableRadical L).map L.subtype
  let R := radicalSylowCentralizer (T : Subgroup G) L
  let E := (solvableRadical W).map W.subtype
  have hWD : W ≤ normalizer (D : Set G) :=
    (sup_le L.le_normalizer hTL).trans
      (normalizer_le_normalizer_characteristic_image L (solvableRadical L))
  have hRT : R ≤ (T : Subgroup G) := radicalSylowCentralizer_le _ _
  have hWE : W ≤ normalizer (E : Set G) := W.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image W (solvableRadical W))
  have hEW : E ≤ W := map_subtype_le _
  let : Group.IsSolvable D := Group.isSolvable_of_surjective
    (L.subtype.subgroupMap_surjective (solvableRadical L))
  let : Group.IsSolvable E := Group.isSolvable_of_surjective
    (W.subtype.subgroupMap_surjective (solvableRadical W))
  apply le_antisymm
  · have hc : ⁅L,R⁆ ≤ D := by
      rw [commutator_comm]
      exact ((le_radicalSylowCentralizer_iff hTL).mp le_rfl).2
    have hLC : L ≤ normalizer ((D ⊔ R : Subgroup G) : Set G) := by
      apply le_normalizer_iff.mpr
      intro l hl c hc'
      have hh : D ⊔ R ≤ (D ⊔ R).comap (MulAut.conj l).toMonoidHom := by
        apply sup_le
        · intro d hd
          exact mem_sup_left (le_normalizer_iff.mp hWD l (mem_sup_left hl) d hd)
        · intro r hr
          have hm := (D ⊔ R).mul_mem
            (mem_sup_left (hc (commutator_mem_commutator hl hr))) (mem_sup_right hr)
          change l * r * l⁻¹ ∈ D ⊔ R
          simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hm
      exact hh hc'
    have hTC : (T : Subgroup G) ≤ normalizer ((D ⊔ R : Subgroup G) : Set G) :=
      (le_inf (le_sup_right.trans hWD) (sylow_normalizes_radicalSylowCentralizer hTL)).trans
        (normalizer_inf_normalizer_le_normalizer_sup D R)
    let : Group.IsNilpotent R := (T.isPGroup'.to_le hRT).isNilpotent
    let : Group.IsSolvable (D ⊔ R : Subgroup G) :=
      Group.isSolvable_sup_of_normalizes D R (hRT.trans (le_sup_right.trans hWD))
    have hCE : D ⊔ R ≤ E := solvable_normal_in_le_radical
      (sup_le ((map_subtype_le _).trans le_sup_left) (hRT.trans le_sup_right))
      (sup_le hLC hTC)
    exact le_inf hRT (le_sup_right.trans hCE)
  · apply (le_radicalSylowCentralizer_iff hTL).mpr
    refine ⟨inf_le_left, ?_⟩
    have hEL : E ≤ normalizer (L : Set G) :=
      hEW.trans (sup_le L.le_normalizer hTL)
    have hCL : ⁅L,E⁆ ≤ L := le_normalizer_iff_commutator_le_left.mp hEL
    have hCE : ⁅L,E⁆ ≤ E :=
      le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans hWE)
    let : Group.IsSolvable (⁅L,E⁆ : Subgroup G) :=
      Group.isSolvable_of_isSolvable_injective (f := inclusion hCE) (inclusion_injective hCE)
    have hCD : ⁅L,E⁆ ≤ D :=
      solvable_normal_in_le_radical hCL (normalizer_commutator_ge_left L E)
    rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_right).trans hCD

/-- The exact Sylow premise used by the canonical Frattini geometry. -/
theorem radicalSylowCentralizer_isSylow (T : Sylow 2 G) {L : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    IsSylowIn 2 (radicalSylowCentralizer T L)
      ((solvableRadical (L ⊔ (T : Subgroup G) : Subgroup G)).map
        (L ⊔ (T : Subgroup G)).subtype) := by
  rw [radicalSylowCentralizer_eq_inf_radical T hTL]
  let W := L ⊔ (T : Subgroup G)
  let E := (solvableRadical W).map W.subtype
  have hn : W ≤ normalizer (E : Set G) := W.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image W (solvableRadical W))
  let : (E.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer hn
  exact IndexTwo.isSylowIn_inf_of_subnormal
    ⟨T.subtype le_sup_right, map_subgroupOf_eq_of_le le_sup_right⟩
    (map_subtype_le _) (inferInstance : (E.subgroupOf W).Normal).isSubnormal

/-- Original 13.1.9 supplies the radical Sylow assertion without any extra premise. -/
theorem radical_sylow_source {T : Sylow 2 G} (h : Hypothesis1311 T)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    IsSylowIn 2 (radicalSylowCentralizer T L)
      ((solvableRadical (L ⊔ (T : Subgroup G) : Subgroup G)).map
        (L ⊔ (T : Subgroup G)).subtype) :=
  radicalSylowCentralizer_isSylow T (radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn)

/-- The source local membership, two-core equality and all residual
Frattini products, with the original Sylow premise discharged. -/
theorem canonical_frattini_geometry {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    canonicalSupplement T L ∈ radicalSupplements T L ∧
      (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 = radicalSylowCentralizer T L ∧
      ∀ B ∈ radicalSupplements T L,
        (solvableRadical B).map B.subtype ⊔
          Chapter1.RadicalNormalizers.normalizerResidual B (radicalSylowCentralizer T L) = B :=
  canonical_frattini_geometry_source h hmany hL hn (radical_sylow_source h hL hn)

/-- The actual prime-field model for the canonical radical quotient,
without a Sylow callback. Identifying the radical with the two-core is
still needed to obtain the source XiQuotient model. -/
theorem canonical_radical_quotient {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ClassicalGroup.IsPSL
      (canonicalSupplement T L ⧸ solvableRadical (canonicalSupplement T L)) 2 p :=
  canonical_radical_quotient_source h hmany hL hn (radical_sylow_source h hL hn)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter1 Chapter1.Section02 Chapter1.Section02.Adequate
open Chapter12.Section02 ChapterA.Section04 Chapter1.RadicalNormalizers
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The actual canonical residual is faithful on its intrinsic module. -/
theorem canonical_intrinsicModule_ne_bot (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    intrinsicSignalizerModule (canonicalSupplement T L) ≠ ⊥ := by
  let Y := canonicalSupplement (T : Subgroup G) L
  let R := radicalSylowCentralizer (T : Subgroup G) L
  let U := normalizerMoved L
  let M := normalizer (L : Set G)
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hTM : (T : Subgroup G) ≤ M := hTL
  have hWM : L ⊔ (T : Subgroup G) ≤ M := sup_le L.le_normalizer hTM
  obtain ⟨hUe,hUne,hUQ,hMU⟩ := faithful_maximal_normalizer_moved h.simpleQTKE hL hTL
  let : IsElementaryAbelian 2 U := hUe
  have hUnorm : M ≤ normalizer (U : Set G) := hMU.ge
  obtain ⟨hY,hcore,_⟩ := canonical_frattini_geometry h hmany hL hn
  have hYL : Y ≤ L := canonicalSupplement_le _ _
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    sylow_normalizes_canonicalSupplement hTL
  have hRT : R ≤ (T : Subgroup G) := radicalSylowCentralizer_le _ _
  have hYR : Y ≤ normalizer (R : Set G) := normalizerResidual_le_normalizer _ _
  have hRY : R ≤ normalizer (Y : Set G) := hRT.trans hTY
  have hRp : IsPGroup 2 R := T.isPGroup'.to_le hRT
  have hYp : IsPPerfect 2 Y := mem_L_isPPerfect hY.1
  have hYQ : (pCore 2 Y).map Y.subtype ≤ R := by
    change Y.pCoreIn 2 ≤ R
    exact (pCoreIn_mono_of_normalizes le_sup_left (sup_le Y.le_normalizer hTY)).trans_eq hcore
  have hcomm : ⁅Y,R⁆ ≤ (pCore 2 Y).map Y.subtype :=
    commutator_le_pCore_of_mutual_normalization Y R hRp hYR hRY
  have hMQT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow M (T.subtype hTM)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM] using hh
  have hUT : U ≤ (T : Subgroup G) := hUQ.trans hMQT
  have hUR : U ≤ R := by
    apply le_trans _ (join_core_le_radicalSylowCentralizer T hTL)
    exact le_pCoreIn_of_normalizes hUe.isPGroup
      (hUT.trans le_sup_right) (hWM.trans hUnorm)
  have hYU : Y ≤ normalizer (U : Set G) := (hYL.trans L.le_normalizer).trans hUnorm
  have hRU : R ≤ normalizer (U : Set G) := (hRT.trans hTM).trans hUnorm
  have hDU : (solvableRadical L).map L.subtype ≤ centralizer (U : Set G) :=
    solvableRadical_centralizes_normalizerMoved h hmany hL.1 hn
  have hUY : ⁅U,Y⁆ = U :=
    (commutator_eq_of_centralizing_sup hY.2 hDU hYU).trans
      (normalizerMoved_commutator_and_card hL.1.1 hUne).1
  have hkernel : ⁅R,Y⁆ ≤ centralizer (U : Set G) := by
    apply le_trans ((commutator_mono le_rfl hYL).trans
      ((le_radicalSylowCentralizer_iff hTL).mp le_rfl).2) hDU
  intro hzero
  have hVzero : signalizerModule Y R = ⊥ := le_bot_iff.mp
    ((signalizerModule_le_intrinsicModule Y R hYp hYR hYQ hcomm).trans hzero.le)
  have hfixed : U ⊓ centralizer (R : Set G) ≤ omegaOneCenterAmbient R := by
    intro u hu
    exact (mem_omegaOneCenterAmbient_iff R u).mpr
      ⟨hUR hu.1, elemPow_eq_one_of_isElementaryAbelian u hu.1,
        mem_centralizer_iff.mp hu.2⟩
  have hfix : ⁅U ⊓ centralizer (R : Set G),Y⁆ = ⊥ := by
    apply le_bot_iff.mp
    calc
      ⁅U ⊓ centralizer (R : Set G),Y⁆ ≤ ⁅omegaOneCenterAmbient R,Y⁆ :=
        commutator_mono hfixed le_rfl
      _ = signalizerModule Y R := by
        rw [signalizerModule_eq_commutator_omegaCenter,commutator_comm]
      _ = ⊥ := hVzero
  exact hUne (hUY.symm.trans
    (hYp.centralizes_of_commuting_fixed Y R U hRp hYU hRU hkernel hfix))

/-- Membership in the actual faithful local family, with no additional
faithfulness or inversion premise. -/
theorem canonical_mem_faithfulLocalComponents (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    canonicalSupplement T L ∈ MainForward.faithfulLocalComponents T := by
  apply (mem_faithfulLocalComponents_iff_module T (h.simpleQTKE.evenCharacteristic T)).mpr
  exact ⟨(canonical_frattini_geometry h hmany hL hn).1.1,
    canonical_intrinsicModule_ne_bot h hmany hL hn⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
open Chapter1 Chapter1.Section02 Chapter12.Section02 Chapter1.RadicalNormalizers
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The original radical intersection eliminates the canonical odd radical. -/
theorem canonical_radical_eq_twoCore_of_intersection (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hi : (solvableRadical (L ⊔ (T : Subgroup G) : Subgroup G)).map
        (L ⊔ (T : Subgroup G)).subtype ⊓
        (canonicalSupplement T L ⊔ (T : Subgroup G)) = radicalSylowCentralizer T L) :
    solvableRadical (canonicalSupplement T L) = pCore 2 (canonicalSupplement T L) := by
  let Y := canonicalSupplement (T : Subgroup G) L
  have hY := (canonical_frattini_geometry h hmany hL hn).1
  have hk := (maximal_nonquasisimple_normalizer_action_source h hmany hL hn).1
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hDR : (solvableRadical Y).map Y.subtype ≤ radicalSylowCentralizer T L := by
    apply le_trans _ hi.le
    apply le_inf
    · exact ((supplement_radical hk hY.2).le.trans inf_le_right).trans
        (radical_le_join_radical hTL)
    · exact (map_subtype_le _).trans le_sup_left
  apply le_antisymm
  · apply (map_le_map_iff_of_injective Y.subtype_injective).mp
    exact le_pCoreIn_of_normalizes
      (T.isPGroup'.to_le (hDR.trans (radicalSylowCentralizer_le _ _)))
      (map_subtype_le _)
      (Y.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Y (solvableRadical Y)))
  · let : Group.IsNilpotent (pCore 2 Y) := pCore_isPGroup.isNilpotent
    exact le_solvableRadical _ inferInstance inferInstance

/-- The same actual PSL₂(p) model becomes the canonical two-core quotient. -/
theorem canonical_twoCore_quotient_of_radical_eq (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hr : solvableRadical (canonicalSupplement T L) = pCore 2 (canonicalSupplement T L)) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧
      ClassicalGroup.IsPSL (XiQuotient (canonicalSupplement T L)) 2 p := by
  obtain ⟨p,hp,hp3,he⟩ := canonical_radical_quotient h hmany hL hn
  exact ⟨p,hp,hp3,he.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hr.symm)⟩

/-- The canonical quotient is quasisimple once the radical equality has
been established. Simplicity comes from its actual local C-component. -/
theorem canonical_quasisimple_of_radical_eq (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hr : solvableRadical (canonicalSupplement T L) = pCore 2 (canonicalSupplement T L)) :
    IsQuasisimple (XiQuotient (canonicalSupplement T L)) := by
  let Y := canonicalSupplement (T : Subgroup G) L
  let C := Y.subgroupOf (Y ⊔ (T : Subgroup G))
  have hY := (canonical_frattini_geometry h hmany hL hn).1.1
  let : IsSimpleGroup (C ⧸ solvableRadical C) := hY.1.isSimpleGroup_quotient_solvableRadical
  let e : C ≃* Y := subgroupOfEquivOfLe le_sup_left
  let er : (C ⧸ solvableRadical C) ≃* (Y ⧸ solvableRadical Y) :=
    QuotientGroup.congr _ _ e (map_solvableRadical_equiv e)
  let eq : (C ⧸ solvableRadical C) ≃* XiQuotient Y :=
    er.trans (QuotientGroup.quotientMulEquivOfEq hr)
  let : IsSimpleGroup (XiQuotient Y) := eq.symm.isSimpleGroup
  let : Group.IsPerfect Y := canonicalSupplement_perfect _ _
  let : Group.IsPerfect (XiQuotient Y) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  have hz : center (XiQuotient Y) = ⊥ :=
    (inferInstance : (center (XiQuotient Y)).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp he))
  exact { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup }

/-- Actual application of the canonical supplement comparison. The
remaining premise is precisely the source radical-intersection assertion. -/
theorem canonical_comparison_of_intersection (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hi : (solvableRadical (L ⊔ (T : Subgroup G) : Subgroup G)).map
        (L ⊔ (T : Subgroup G)).subtype ⊓
        (canonicalSupplement T L ⊔ (T : Subgroup G)) = radicalSylowCentralizer T L) :
    canonicalSupplement T L ∈ radicalSupplements T L ∧
      (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 = radicalSylowCentralizer T L ∧
      ∀ B ∈ radicalSupplements T L,
        normalizerResidual B (radicalSylowCentralizer T L) = canonicalSupplement T L ∧
        (solvableRadical B).map B.subtype ⊔ canonicalSupplement T L = B ∧
        canonicalSupplement T L ≤ B ∧
        (((solvableRadical B).map B.subtype : Subgroup G) : Set G) *
          (canonicalSupplement T L : Set G) = (B : Set G) := by
  exact canonical_supplement_comparison_source h hmany hL hn (radical_sylow_source h hL hn)
    (canonical_quasisimple_of_radical_eq h hmany hL hn
      (canonical_radical_eq_twoCore_of_intersection h hmany hL hn hi))

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements
