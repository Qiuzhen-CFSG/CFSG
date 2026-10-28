module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Setup
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.BlockExclusion
public import Theory.GroupTheory.ConjugateSpanKernel
public import Theory.Representation.NormalElementaryQuotient.BestOffender

/-!
# The original commutator module and its Thompson offender

For W = ⟨ZS^X⟩ and U = [W,X], normal generation gives W = ZS U.
The source places W, and hence U, in QI = O₂(KS). Since QI centralizes
ZS, its centralizers of W and U agree. Thus the Thompson argument used
on W applies to U itself: the actual action image contains a best offender.
The input core identity is the model calculation still needed in the
orthogonal row; it is stated on the literal extension XQI.

Source: Aschbacher--Smith, 15.2.23(c), printed p.1117, referring to the
Thompson argument on p.1115 and B.2.5--10.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open Section01 PlaneUniquenessPreceding
variable {G : Type*} [Group G]

/-- The original moved module stays inside the original conjugate span. -/
theorem U_le_span (X ZS : Subgroup G) : U X ZS ≤ conjugateSpanBy ZS X :=
  le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy ZS X)

/-- Normal generation separates the seed from its displacements. -/
theorem span_eq_seed_sup_U (X ZS : Subgroup G) :
    conjugateSpanBy ZS X = ZS ⊔ U X ZS := by
  have hb : conjugateSpanBy ZS ⊥ = ZS :=
    le_antisymm (conjugateSpanBy_le le_rfl bot_le) (le_conjugateSpanBy ZS ⊥)
  simpa only [sup_bot_eq, hb, U] using
    conjugateSpanBy_sup_eq_span_sup_commutator ZS X ⊥ bot_le

/-- Any subgroup fixing the seed has the same centralizer on W and U. -/
theorem centralizer_U_eq_span {X ZS A : Subgroup G}
    (hA : A ≤ centralizer (ZS : Set G)) :
    A ⊓ centralizer (U X ZS : Set G) =
      A ⊓ centralizer (conjugateSpanBy ZS X : Set G) := by
  apply le_antisymm
  · refine le_inf inf_le_left ?_
    rw [span_eq_seed_sup_U]
    exact le_centralizer_iff.mpr (sup_le
      (le_centralizer_iff.mp (inf_le_left.trans hA))
      (le_centralizer_iff.mp inf_le_right))
  · exact inf_le_inf_left _ (centralizer_le (U_le_span X ZS))

variable [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- Elementarity is inherited from Ω₁Z(O₂(I)), not assumed as model data. -/
theorem U_elementary (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I) (hXI : X ≤ I) :
    IsElementaryAbelian 2 (U X ZS) := by
  let := d.plane_span_elementary hI hfit hXI
  exact IsElementaryAbelian.of_injective (inclusion (U_le_span X ZS))
    (inclusion_injective (U_le_span X ZS))

/-- Containment in the literal QI, needed for the maximum-elementary argument. -/
theorem U_le_QI (hI : PlaneEscapes Mc ZS I)
    (hfit : generalizedFitting I = pCore 2 I) (hXI : X ≤ I) :
    U X ZS ≤ QI H T ZS :=
  (U_le_span X ZS).trans (d.plane_span_le_planeParabolicCore hI hfit hXI)

/-- Relative normality of X in I gives normalization of the original U by XQI. -/
theorem U_normalized (hI : PlaneEscapes Mc ZS I)
    (hn : I ≤ normalizer (X : Set G)) :
    X ⊔ QI H T ZS ≤ normalizer (U X ZS : Set G) := by
  have hQI : QI H T ZS ≤ I := (pCoreIn_le 2 _).trans
    ((d.residual_sup_planeSylow_le hI).trans inf_le_right)
  have hX : X ⊔ QI H T ZS ≤ normalizer (X : Set G) :=
    sup_le X.le_normalizer (hQI.trans hn)
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (⁅conjugateSpanBy ZS X, X⁆).map (MulAut.conj g).toMonoidHom = _
  have hw : (conjugateSpanBy ZS X).map (MulAut.conj g).toMonoidHom =
      conjugateSpanBy ZS X := mem_normalizer_iff_map_conj_eq.mp
        (d.plane_span_normalized hI hn hg)
  have hx : X.map (MulAut.conj g).toMonoidHom = X :=
    mem_normalizer_iff_map_conj_eq.mp (hX hg)
  rw [map_commutator, hw, hx]
  rfl

/-- The actual QI-action has the same kernel on U and on the whole span. -/
theorem QI_centralizer_U_eq_span :
    QI H T ZS ⊓ centralizer (U X ZS : Set G) =
      QI H T ZS ⊓ centralizer (conjugateSpanBy ZS X : Set G) :=
  centralizer_U_eq_span ((pCoreIn_le 2 _).trans
    (sup_le d.residual_centralizes inf_le_right))

/-- The genuine FF* witness for the orthogonal row, on U rather than on an
unrelated section. Only the marked core calculation remains an input. -/
theorem U_bestOffender
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hcore : (X ⊔ QI H T ZS).pCoreIn 2 =
      QI H T ZS ⊓ centralizer (conjugateSpanBy ZS X : Set G)) :
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
          (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) (A.map q) := by
  classical
  dsimp only
  let E := X ⊔ QI H T ZS
  let W := (U X ZS).subgroupOf E
  let : W.Normal := normal_subgroupOf_of_le_normalizer (U_normalized d hI hn)
  let : IsElementaryAbelian 2 (U X ZS) := U_elementary d hI hfit hXI
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf
    ((U_le_QI d hI hfit hXI).trans le_sup_right)
  let q := QuotientGroup.mk' (centralizer (W : Set E))
  let R := (QI H T ZS).subgroupOf E
  have hR : R.map E.subtype = QI H T ZS := map_subgroupOf_eq_of_le le_sup_right
  have hJ : (elementaryAbelianMaxJ R).map E.subtype =
      elementaryAbelianMaxJ (QI H T ZS) := by
    rw [← elementaryAbelianMaxJ_map_injective E.subtype E.subtype_injective, hR]
  have hj : ¬ elementaryAbelianMaxJ R ≤ q.ker := by
    intro hh
    apply d.planeParabolicCore_thompson_not_le_core hI hout (hcore.le.trans inf_le_left)
    change elementaryAbelianMaxJ (QI H T ZS) ≤ (X ⊔ QI H T ZS).pCoreIn 2
    rw [hcore, ← QI_centralizer_U_eq_span d]
    refine le_inf (sSup_le fun _ hA => hA.1) ?_
    rw [← hJ]
    rintro _ ⟨a, ha, rfl⟩ u hu
    let uE : E := ⟨u, ((U_le_QI d hI hfit hXI).trans le_sup_right) hu⟩
    have hc : a ∈ centralizer (W : Set E) := by
      simpa only [q, QuotientGroup.ker_mk'] using hh ha
    exact congrArg E.subtype (hc uE hu)
  obtain ⟨A, hA, hne⟩ : ∃ A ∈ elementaryAbelianMaxSubgroups R, A.map q ≠ ⊥ := by
    by_contra! hh
    exact hj (sSup_le fun A hA => (Subgroup.map_eq_bot_iff A).mp (hh A hA))
  exact ⟨A, hA, Representation.NormalElementaryQuotient.maxElementary_isBestOffender
    W q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) R A
    (fun _ hw => U_le_QI d hI hfit hXI hw) hA hne⟩

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
