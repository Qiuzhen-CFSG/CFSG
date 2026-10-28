module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Action
public import Theory.GroupTheory.PGroup.NormalSupplementKernel

/-!
# The actual kernel and FF* witness on the original U

Put E=XQI. Its two-core is normal in XS, so it lies in S and centralizes
ZS. Normality under X then makes it centralize the whole conjugate span.
K≤X also makes this core normal in KS, putting it inside QI.
Conversely, faithfulness of the X/O₂(X)-action makes the kernel on X a
two-group. The normal supplement E=XQI makes the full kernel a two-group.
This proves the marked core identity and constructs the genuine FF* witness.

Source: Aschbacher--Smith 15.2.23(c), printed p.1117, using B.2.5--10.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open Section01 PlaneUniquenessPreceding
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

omit [Finite G] in
private theorem conjugation_kernel (A W : Subgroup G)
    (hn : A ≤ normalizer (W : Set G)) :
    (W.normalizerMonoidHom.comp (inclusion hn)).ker.map A.subtype =
      A ⊓ centralizer (W : Set G) := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨a.property,?_⟩
    intro u hu
    have he := congrArg (fun f : MulAut W => (f ⟨u,hu⟩ : G)) ha
    change (a : G) * u * (a : G)⁻¹ = u at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hx
    refine ⟨⟨x,hx.1⟩,?_,rfl⟩
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    change x * (u : G) * x⁻¹ = u
    rw [← hx.2 u u.property, mul_inv_cancel_right]

include d in
/-- The core bound follows from the original Sylow and K-containment clauses. -/
theorem extension_core_le_seed_kernel
    (hI : PlaneEscapes Mc ZS I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G))
    (hKX : (pResidual 2 H).map H.subtype ≤ X) :
    (X ⊔ QI H T ZS).pCoreIn 2 ≤
      QI H T ZS ⊓ centralizer (conjugateSpanBy ZS X : Set G) := by
  let S := planeSylow T ZS
  let E := X ⊔ QI H T ZS
  have hSI : S ≤ I :=
    (le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  have hQS : QI H T ZS ≤ S := d.planeParabolicCore_le_plane hI
  have hSQ : S ≤ normalizer (QI H T ZS : Set G) :=
    le_sup_right.trans ((KS H T ZS).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hSE : S ≤ normalizer (E : Set G) :=
    (le_inf (hSI.trans hn) hSQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hES : E ≤ X ⊔ S := sup_le le_sup_left (hQS.trans le_sup_right)
  have hESn : X ⊔ S ≤ normalizer (E : Set G) :=
    sup_le (le_sup_left.trans E.le_normalizer) hSE
  have hRS : E.pCoreIn 2 ≤ S := by
    obtain ⟨P,hP⟩ := (show Chapter1.IsSylowIn 2 S I from d.sylow_in_escape hI).restrict
      (show S ≤ X ⊔ S from le_sup_right) (sup_le hXI hSI)
    exact (pCoreIn_mono_of_normalizes hES hESn).trans ((pCoreIn_le_sylow _ P).trans_eq hP)
  have hnR : X ⊔ S ≤ normalizer (E.pCoreIn 2 : Set G) :=
    hESn.trans (normalizer_le_normalizer_characteristic_image E (pCore 2 E))
  have hRQ : E.pCoreIn 2 ≤ QI H T ZS :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 E) (hRS.trans le_sup_right)
      ((sup_le (hKX.trans le_sup_left) le_sup_right).trans hnR)
  exact le_inf hRQ (le_centralizer_conjugateSpanBy_of_normalizes _ ZS X
    (le_sup_left.trans hnR) (hRS.trans inf_le_right))

include d in
/-- The action kernel is a two-group because E is the normal supplement XQI. -/
theorem extension_kernel_isTwoGroup
    (hI : PlaneEscapes Mc ZS I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G))
    (hfaith : X ⊓ centralizer (U X ZS : Set G) ≤ X.pCoreIn 2) :
    IsPGroup 2 ((X ⊔ QI H T ZS) ⊓ centralizer (U X ZS : Set G) : Subgroup G) := by
  let E := X ⊔ QI H T ZS
  let L := X.subgroupOf E
  let P := (QI H T ZS).subgroupOf E
  have hEI : E ≤ I := sup_le hXI
    ((pCoreIn_le 2 _).trans ((d.residual_sup_planeSylow_le hI).trans inf_le_right))
  let : L.Normal := normal_subgroupOf_of_le_normalizer (hEI.trans hn)
  let f : E →* MulAut (U X ZS) :=
    (U X ZS).normalizerMonoidHom.comp (inclusion (U_normalized d hI hn))
  have hk : IsPGroup 2 (f.comp L.subtype).ker := by
    let r : (f.comp L.subtype).ker →* X.pCoreIn 2 :=
      ((E.subtype.comp L.subtype).comp (f.comp L.subtype).ker.subtype).codRestrict _ (by
        intro x
        apply hfaith
        refine ⟨x.val.property,?_⟩
        intro u hu
        have he := congrArg (fun a : MulAut (U X ZS) => (a ⟨u,hu⟩ : G)) x.property
        change (x.val.val : G) * u * (x.val.val : G)⁻¹ = u at he
        exact (mul_inv_eq_iff_eq_mul.mp he).symm)
    exact (isPGroup_pCoreIn 2 X).of_injective r (by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : X.pCoreIn 2 => (x : G)) hab)
  have hgen : L ⊔ P = ⊤ := by
    apply map_injective E.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show X ≤ E from le_sup_left),
      map_subgroupOf_eq_of_le (show QI H T ZS ≤ E from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hp := f.kernel_isPGroup_of_normal_supplement L P
    ((isPGroup_pCoreIn 2 (KS H T ZS)).comap_subtype) hgen hk
  rw [← conjugation_kernel E (U X ZS) (U_normalized d hI hn)]
  exact hp.map E.subtype

include d in
/-- The precise core identity is proved from Sylow geometry and the action kernel. -/
theorem extension_core_eq_seed_kernel
    (hI : PlaneEscapes Mc ZS I) (hXI : X ≤ I)
    (hn : I ≤ normalizer (X : Set G))
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hfaith : X ⊓ centralizer (U X ZS : Set G) ≤ X.pCoreIn 2) :
    (X ⊔ QI H T ZS).pCoreIn 2 =
      QI H T ZS ⊓ centralizer (conjugateSpanBy ZS X : Set G) := by
  apply le_antisymm (extension_core_le_seed_kernel d hI hXI hn hKX)
  have hc : (X ⊔ QI H T ZS) ⊓ centralizer (U X ZS : Set G) ≤
      (X ⊔ QI H T ZS).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (extension_kernel_isTwoGroup d hI hXI hn hfaith) inf_le_left
      ((le_inf (X ⊔ QI H T ZS).le_normalizer
        ((U_normalized d hI hn).trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf)
  exact (inf_le_inf le_sup_right (centralizer_le (U_le_span X ZS))).trans hc

include d in
/-- Faithfulness uses the literal X/O₂(X) action, hence gives its actual ambient kernel. -/
theorem U_centralizer_le_core_of_faithful
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    (hfaith : Function.Injective (U_representation d hI hfit hXI hn)) :
    X ⊓ centralizer (U X ZS : Set G) ≤ X.pCoreIn 2 := by
  let := U_elementary d hI hfit hXI
  intro x hx
  have he : QuotientGroup.mk' (pCore 2 X) ⟨x,hx.1⟩ = 1 := by
    apply hfaith
    apply LinearMap.ext
    intro u
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [U_representation_apply, map_one]
    change x * (u.toMul : G) * x⁻¹ = (u.toMul : G)
    rw [← hx.2 u.toMul u.toMul.property, mul_inv_cancel_right]
  exact mem_map_of_mem X.subtype ((QuotientGroup.eq_one_iff _).mp he)

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear

namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open Section01 PlaneUniquenessPreceding
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

/-- A genuine best offender on U, with the marked core identity discharged. -/
theorem U_bestOffender_of_faithful
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hfaith : Function.Injective (U_representation d hI hfit hXI hn)) :
    let E := X ⊔ QI H T ZS
    let W := (U X ZS).subgroupOf E
    let : W.Normal := normal_subgroupOf_of_le_normalizer (U_normalized d hI hn)
    let : IsElementaryAbelian 2 W := by
      let := U_elementary d hI hfit hXI
      exact IsElementaryAbelian.subgroupOf
        ((U_le_QI d hI hfit hXI).trans le_sup_right)
    let q := QuotientGroup.mk' (centralizer (W : Set E))
    ∃ A ∈ elementaryAbelianMaxSubgroups ((QI H T ZS).subgroupOf E),
      Representation.BinaryOffender.IsBestOffender
        (Representation.NormalElementaryQuotient.representation W q
          (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) (A.map q) :=
  U_bestOffender d hI hfit hXI hn hout
    (extension_core_eq_seed_kernel d hI hXI hn hKX
      (U_centralizer_le_core_of_faithful d hI hfit hXI hn hfaith))

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
