module
public import CFSG.Quasithin.Chapter14.Section06.SourceFactorMovement
public import Theory.GroupTheory.NormalFourCentralizer

/-!
# The original two cores on the common Sylow subgroup

In a minimal solvable outside group J, its two-core Q cannot centralize the
original plane V. Otherwise normality makes Q centralize the full span U,
putting U in the omega-center of Q. Original 14.6.1(5) then makes the lifted
odd residual centralize U, contrary to the central-line movement in 14.6.2.

The centralizer R=C_T(V)=O₂(LT) has index at most two in T. Since Q crosses
R, the two cores generate T, and their literal quotient images show that
R maps onto the entire Sylow image in J/O₂(J). The last theorem constructs
this compatibility for the minimal J selected from the original odd-core
counterexample. Excluding the singleton elementary-nine case of 14.6.12(2)
still requires the remaining simultaneous local or global geometry.

Source: Aschbacher--Smith, 14.6.1(5), 14.6.2 and the setup for 14.6.12,
printed pp.1020--1021,1030--1031.
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

include hG hempty hM hu hmany hcard e hab


/-- The original solvable two-core acts nontrivially on the source plane. -/
theorem source_solvable_minimal_core_moves_plane
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J) :
    ¬ J.pCoreIn 2 ≤ centralizer (localModule T M : Set G) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  have h : D.Hypothesis := source_rankTwo_f9_hypothesis
    hG T hempty hM hu hmany hcard e hab J hJ.1
  let : IsElementaryAbelian 2 D.UH := h.UH_elementary_of_V_le_QH
    ((le_conjugateSpanBy D.V D.H).trans h.UH_le_QH)
  obtain ⟨p,hp,hE,_,hne,_⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hu hmany hcard e hab J hJ hs
  let : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> decide⟩
  let : IsElementaryAbelian p (pResidual 2 (J ⧸ pCore 2 J)) := hE
  let B := pResidual 2 (J ⧸ pCore 2 J)
  let A := B.comap (QuotientGroup.mk' (pCore 2 J))
  let X := ((pResidual 2 A).map A.subtype).map J.subtype
  have hpoint : D.V₁ ≤ ⁅D.UH,X⁆ :=
    source_point_le_lifted_odd_factor hG T hempty hM hu hmany hcard e hab J hJ hs B le_rfl hne
  have hBf : B ≤ generalizedFitting (J ⧸ pCore 2 J) :=
    (show B ≤ fittingSubgroup (J ⧸ pCore 2 J) from
      le_sSup ⟨inferInstance,inferInstance⟩).trans le_sup_left
  have hXf : X ≤ ChapterA.Section04.twoGeneralizedFittingPreimage J :=
    map_mono ((map_subtype_le _).trans (comap_mono hBf))
  have hXc : X ≤ centralizer (omegaOneCenterAmbient D.QH : Set G) :=
    hXf.trans (source_generalizedFittingPreimage_centralizes_omegaCore
      hG T hempty hJ.1 h.H_centralizes)
  intro hQ
  have hN : J ≤ normalizer (D.QH : Set G) := by
    change J ≤ normalizer (J.pCoreIn 2 : Set G)
    have hh := (pCore 2 J).le_normalizer_map J.subtype
    simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hQU : D.QH ≤ centralizer (D.UH : Set G) :=
    le_centralizer_conjugateSpanBy_of_normalizes D.QH D.V D.H hN hQ
  have hUomega : D.UH ≤ omegaOneCenterAmbient D.QH := by
    intro u hu
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨h.UH_le_QH hu,elemPow_eq_one_of_isElementaryAbelian u hu,
        (le_centralizer_iff.mp hQU) hu⟩
  have hcomm : ⁅D.UH,X⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp (hXc.trans (centralizer_le hUomega)))
  have hz : D.V₁ = ⊥ := bot_unique (hpoint.trans hcomm.le)
  have hc := h.point_card
  norm_num [hz] at hc

/-- The two original cores generate the same Sylow subgroup. -/
theorem source_solvable_minimal_compatible_cores
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J) :
    let R := (T : Subgroup G) ⊓ centralizer (localModule T M : Set G)
    R ⊔ J.pCoreIn 2 = (T : Subgroup G) ∧
      (R.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) =
        ((T : Subgroup G).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  have h : D.Hypothesis := source_rankTwo_f9_hypothesis
    hG T hempty hM hu hmany hcard e hab J hJ.1
  let V := D.V.subgroupOf (T : Subgroup G)
  let R := (T : Subgroup G) ⊓ centralizer (D.V : Set G)
  let C := R.subgroupOf (T : Subgroup G)
  let Q := D.QH.subgroupOf (T : Subgroup G)
  have hVnormal : V.Normal := normal_subgroupOf_of_le_normalizer h.T_normalizes_V
  let : V.Normal := hVnormal
  let : IsElementaryAbelian 2 D.V := h.elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf h.V_le_T
  have hVcard : Nat.card V = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe h.V_le_T).toEquiv).trans hcard
  have hC : C = centralizer (V : Set (T : Subgroup G)) := by
    ext t
    constructor
    · intro ht v hv
      apply Subtype.ext
      exact ht.2 v hv
    · intro ht
      refine ⟨t.property,?_⟩
      intro v hv
      exact congrArg Subtype.val (ht ⟨v,h.V_le_T hv⟩ hv)
  have hnot : ¬ Q ≤ C := by
    intro hc
    apply source_solvable_minimal_core_moves_plane
      hG T hempty hM hu hmany hcard e hab J hJ hs
    intro q hq
    exact (hc (show (⟨q,h.QH_le_T hq⟩ : T) ∈ Q from hq)).2
  have hci : C.index = 2 := by
    have hb : C.index ≤ 2 := by
      rw [hC]
      exact centralizer_index_le_two_of_normal_four T.isPGroup' V hVcard
    have hzero := C.index_ne_zero_of_finite
    have hone : C.index ≠ 1 := fun he => hnot ((index_eq_one.mp he) ▸ le_top)
    omega
  have hjoin : C ⊔ Q = ⊤ := by
    have he := relIndex_mul_index (show C ≤ C ⊔ Q from le_sup_left)
    rw [hci] at he
    have hp : (C.relIndex (C ⊔ Q) * (C ⊔ Q).index).Prime := he.symm ▸ Nat.prime_two
    rcases Nat.prime_mul_iff.mp hp with ⟨_,h1⟩ | ⟨_,h1⟩
    · exact index_eq_one.mp h1
    · exact (hnot (le_sup_right.trans (relIndex_eq_one.mp h1))).elim
  have hRQ : R ⊔ D.QH = (T : Subgroup G) := by
    have hh := congrArg (fun A : Subgroup (T : Subgroup G) => A.map (T : Subgroup G).subtype) hjoin
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show R ≤ (T : Subgroup G) from inf_le_left),
      map_subgroupOf_eq_of_le h.QH_le_T,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  refine ⟨hRQ,?_⟩
  have hi : R.subgroupOf J ⊔ pCore 2 J = (T : Subgroup G).subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (inf_le_left.trans h.T_le_H),
      map_subgroupOf_eq_of_le h.T_le_H]
    exact hRQ
  have hh := congrArg (fun A : Subgroup J => A.map (QuotientGroup.mk' (pCore 2 J))) hi
  simpa only [Subgroup.map_sup,QuotientGroup.map_mk'_self,sup_bot_eq] using hh

/-- An actual odd-core counterexample supplies a minimal solvable subgroup
with the original two-core compatibility, on the same T and quotient map. -/
theorem source_oddCore_counterexample_compatible_cores
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hne : pPrimeCore 2 (H ⧸ pCore 2 H) ≠ ⊥) :
    ∃ (J : Subgroup G), J ∈ Chapter3.HStar (T : Subgroup G) M ∧
      J ≤ H ∧ Group.IsSolvable J ∧
      ¬ J.pCoreIn 2 ≤ centralizer (localModule T M : Set G) ∧
      (let R := (T : Subgroup G) ⊓ centralizer (localModule T M : Set G)
       R ⊔ J.pCoreIn 2 = (T : Subgroup G) ∧
       (R.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) =
         ((T : Subgroup G).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) := by
  obtain ⟨J,hJH,hJ,hs⟩ := source_solvable_minimal_outside_of_oddCore
    hG T hempty hM hu hmany hcard e hab H hH hne
  exact ⟨J,hJ,hJH,hs,
    source_solvable_minimal_core_moves_plane hG T hempty hM hu hmany hcard e hab J hJ hs,
    source_solvable_minimal_compatible_cores hG T hempty hM hu hmany hcard e hab J hJ hs⟩

end CFSG.Quasithin.Chapter14.Section06
