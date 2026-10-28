module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCommonSpace
public import Theory.GroupTheory.CubicCoreCentralizer
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryConjugationSection.PairingCentralizer

/-!
# The source pairing with the full local core retained

For each original local overgroup I with normal point residual B=L₁,
the central commutator constructs the literal dual sections
U_I/C_{U_I}(O₂(I)) and O₂(I)/C_{O₂(I)}(U_I). Restricting their functionals
to any subgroup of U_I computes its actual centralizer index.

The point cubic has no fixed vector on U_I/V₁. Coprime decomposition
and the three-subgroups lemma therefore give equal pairing radicals for
O₂(B) and O₂(I). The original commutator generation places U_I in O₂(B).
Applying duality again gives equal centralizer indices on every subgroup
of U_I, hence O₂(I)=O₂(B) C_{O₂(I)}(U_I). This retains the central factor;
neither core equality nor C_{U_I}(O₂(I))=V₁ is asserted.

LargePrimeEndpointPairing applies this comparison to both endpoints of
the same minimal five-core witness and common eight-group. Its nonzero
pairing restriction, required to exclude the cubic image, remains open.
Source: Aschbacher–Smith, 14.5.21(1) and 14.7.6, printed pp.1019 and
1044–1045, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Subgroup Theory.GroupTheory Representation
open Chapter12.Section08 CriticalFusion.Source
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open scoped commutatorElement IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

/-- The exact source pairing for any original local overgroup, before
identifying its radical with a point or restricting to a quintic support. -/
theorem local_core_duality
    (I : Subgroup G)
    (hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis)
    [IsElementaryAbelian 2 (F.UH I)] :
    ∃ (ρ : Representation (ZMod 2) I
        (Additive (F.UH I ⧸ ((F.UH I) ⊓ centralizer (I.pCoreIn 2 : Set G)).subgroupOf (F.UH I))))
      (sU : BinaryConjugationSection I (F.UH I)
        ((F.UH I) ⊓ centralizer (I.pCoreIn 2 : Set G)) ρ)
      (sQ : BinaryConjugationSection I (I.pCoreIn 2)
        (I.pCoreIn 2 ⊓ centralizer (F.UH I : Set G)) ρ.dual),
      (∀ (q : I.pCoreIn 2) (u : F.UH I),
        (sQ.coordinates q).toAdd (sU.coordinates u).toAdd = 0 ↔
          ⁅(q : G),(u : G)⁆ = 1) ∧
      (∀ C : Subgroup G, C ≤ F.UH I →
        (centralizer (C : Set G)).relIndex (I.pCoreIn 2) = Nat.card (sU.imageSpace C)) := by
  have hN : I ≤ normalizer (I.pCoreIn 2 : Set G) :=
    I.le_normalizer.trans (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hcomm : ⁅I.pCoreIn 2,F.UH I⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact hf.commutator_UH_QH_le_point
  obtain ⟨ρ,sU,sQ,hpair,_⟩ := BinaryConjugationSection.exists_central_duality
    I (I.pCoreIn 2) (F.UH I) (F.Vi 1) (pCoreIn_le 2 I) hf.UH_le_H
    hN (le_normalizer_conjugateSpanBy V I)
    ((hf.point_lt.le.trans (le_conjugateSpanBy _ _)).trans hf.UH_le_QH)
    (le_centralizer_iff.mp hf.H_centralizes) hcomm hf.point_card
  exact ⟨ρ,sU,sQ,hpair,fun C hC => sU.centralizer_index_of_dual_pairing sQ hpair C hC⟩

/-- On any normalized subspace of the original span containing the point,
the point-residual core and the full local core have equal pairing radicals. -/
theorem local_point_core_radical
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hLI : F.Li L 1 ≤ I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis)
    (C : Subgroup G) (hZC : F.Vi 1 ≤ C) (hCU : C ≤ F.UH I)
    (hNC : F.Li L 1 ≤ normalizer (C : Set G)) :
    C ⊓ centralizer ((F.Li L 1).pCoreIn 2 : Set G) =
      C ⊓ centralizer (I.pCoreIn 2 : Set G) := by
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le hCU
  exact cubic_core_centralizer_eq I (F.Li L 1) C (F.Vi 1) hLI
    ((normal_subgroupOf_iff_le_normalizer hLI).mp hn) hNC
    ((commutator_mono hCU le_rfl).trans hf.commutator_UH_QH_le_point)
    (le_centralizer_iff.mp hf.H_centralizes)
    (local_common_space_fixed_line h structural I hLI hn a hf C hZC hCU)
    (pointResidual_core_quotient_card h structural)


/-- Normality places the full local span inside the original point core. -/
theorem local_span_le_point_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (I : Subgroup G) (hLI : F.Li L 1 ≤ I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    F.UH I ≤ (F.Li L 1).pCoreIn 2 := by
  let := h.chosen.elementary
  have hN := (normal_subgroupOf_iff_le_normalizer hLI).mp hn
  have hm : ⁅F.UH I,F.Li L 1⁆ = F.UH I :=
    (conjugateSpanBy_eq_commutator_of_seed V I (F.Li L 1) (F.Li L 1)
      hLI hN le_rfl (seed_commutator h F)).symm
  have hUB : F.UH I ≤ F.Li L 1 := by
    rw [←hm]
    exact le_normalizer_iff_commutator_le_right.mp (a.le_local.trans hN)
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 (F.UH I))
    hUB (hLI.trans a.normalizes)

/-- The two original cores have the same centralizer index on every
subgroup of the span, using the actual source pairing radical. -/
theorem local_point_core_pairing_indices
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hLI : F.Li L 1 ≤ I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis)
    (C : Subgroup G) (hCU : C ≤ F.UH I) :
    (centralizer (C : Set G)).relIndex ((F.Li L 1).pCoreIn 2) =
      (centralizer (C : Set G)).relIndex (I.pCoreIn 2) ∧
    (centralizer (C : Set G)).relIndex (I.pCoreIn 2) =
      ((F.UH I) ⊓ centralizer (I.pCoreIn 2 : Set G)).relIndex C := by
  let P := (F.Li L 1).pCoreIn 2
  have hN := (normal_subgroupOf_iff_le_normalizer hLI).mp hn
  have hPQ : P ≤ I.pCoreIn 2 := pCoreIn_mono_of_normalizes hLI hN
  have hUP := local_span_le_point_core h I hLI hn a
  have hNP : I ≤ normalizer (P : Set G) :=
    hN.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 (F.Li L 1)))
  obtain ⟨ρ,sU,sQ,hpair,hindex⟩ := local_core_duality I hf
  have hQindex := (hindex C hCU).trans (sU.imageSpace_card_eq_relIndex C hCU)
  have hcomm : ⁅P,F.UH I⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hPQ).trans hf.commutator_UH_QH_le_point
  obtain ⟨τ,tU,tP,htpair,_⟩ := BinaryConjugationSection.exists_central_duality
    I P (F.UH I) (F.Vi 1) (hPQ.trans (pCoreIn_le 2 I)) a.le_local hNP a.normalizes
    (a.kernel_le.trans hUP) (le_centralizer_iff.mp hf.H_centralizes) hcomm hf.point_card
  have hPindex := (tU.centralizer_index_of_dual_pairing tP htpair C hCU).trans
    (tU.imageSpace_card_eq_relIndex C hCU)
  have hrad := local_point_core_radical h structural I hLI hn a hf
    (F.UH I) a.kernel_le le_rfl (hLI.trans a.normalizes)
  change (F.UH I) ⊓ centralizer (P : Set G) = _ at hrad
  rw [hrad] at hPindex
  exact ⟨hPindex.trans hQindex.symm,hQindex⟩

/-- The full core is the point core times its literal span centralizer.
The central factor is retained, so no equality of the two cores is used. -/
theorem local_point_core_supplement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hLI : F.Li L 1 ≤ I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis) :
    (F.Li L 1).pCoreIn 2 ⊔ (I.pCoreIn 2 ⊓ centralizer (F.UH I : Set G)) = I.pCoreIn 2 := by
  let P := (F.Li L 1).pCoreIn 2
  let Q := I.pCoreIn 2
  let C := Q ⊓ centralizer (F.UH I : Set G)
  have hPQ : P ≤ Q := pCoreIn_mono_of_normalizes hLI
    ((normal_subgroupOf_iff_le_normalizer hLI).mp hn)
  have hCQ : C ≤ Q := inf_le_left
  have hjoin : P ⊔ C ≤ Q := sup_le hPQ hCQ
  let : (C.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer
    ((le_inf Q.le_normalizer ((pCoreIn_le 2 I).trans
      (a.normalizes.trans (normalizer_le_normalizer_centralizer _)))).trans
        inf_normalizer_le_normalizer_inf)
  have hrel : C.relIndex (P ⊔ C) = C.relIndex P := by
    have he := relIndex_sup_right (P.subgroupOf Q) (C.subgroupOf Q)
    rw [←subgroupOf_sup hPQ hCQ,relIndex_subgroupOf hjoin,relIndex_subgroupOf hPQ] at he
    exact he
  have hind : C.relIndex P = C.relIndex Q := by
    have hi := (local_point_core_pairing_indices h structural I hLI hn a hf (F.UH I) le_rfl).1
    have hp : C.subgroupOf P = (centralizer (F.UH I : Set G)).subgroupOf P := by
      ext p
      exact ⟨fun hp => hp.2,fun hp => ⟨hPQ p.property,hp⟩⟩
    change (C.subgroupOf P).index = _
    rw [hp]
    change (centralizer (F.UH I : Set G)).relIndex P =
      (Q ⊓ centralizer (F.UH I : Set G)).relIndex Q
    rw [inf_relIndex_left]
    exact hi
  have hm := relIndex_mul_relIndex C (P ⊔ C) Q le_sup_right hjoin
  rw [hrel,hind] at hm
  have hnzero : C.relIndex Q ≠ 0 := by
    change Nat.card (Q ⧸ C.subgroupOf Q) ≠ 0
    exact Nat.card_ne_zero.mpr ⟨inferInstance,inferInstance⟩
  have hone : (P ⊔ C).relIndex Q = 1 := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hnzero)
    simpa only [mul_one] using hm
  exact le_antisymm hjoin (relIndex_eq_one.mp hone)


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
