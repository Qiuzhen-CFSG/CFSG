module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSparseSections
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSevenWitness
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalJankoTwoWitness
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalMathieuComplete

/-!
# Exhaustive remaining carriers for the original local Cartan escape

Inspect the full Theorem C model of the same selected two-core image,
using the genuine A.3.6 alternatives. Every classical and alternating
row is either excluded by the existing original-input theorems or gives
the complete binary-triality endpoint. The A₇, J₂ and M₂₃ rows invoke
their constructed witnesses and give the full original-W conclusion,
including the relative component in the omega centralizer.

The remaining simple carriers are exactly the still-open M₂₄, Held, HS
and Rudvalis branches. In HS and Rudvalis the new proper-section bound
constructs the original PSL₂(4) residual and cubic right Hall. The two
noncentral-Fitting A.3.6 alternatives retain their full mathematical
content on the literal image in Y/O₂(Y). No quasisimplicity or shortlist
is an input, and the general Ree family is included in the rank-two
case analysis. This is a reduction, not the full SourceLocalCartanEscape.

The literal Chapter12 consumer keeps the chosen whole reduced module
and both original Hall conditions. The omitted branch exclusions and
final source assembly remain with this theorem-family owner.
Source: Aschbacher–Smith A.3.6, A.3.12 and 5.1.12–13,
printed pp.43–48,635–638, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

private theorem rankTwo_transport {X Z : Type*} [Group X] [Group Z]
    (e : X ≃* Z) (h : RankTwoTheoremC Z) : RankTwoTheoremC X := by
  cases h with
  | linear f hf hm => exact .linear f hf (hm.of_mulEquiv e)
  | symplectic f hf hm => exact .symplectic f hf (hm.of_mulEquiv e)
  | g2 f hf hm => exact .g2 f hf (hm.of_mulEquiv e)
  | triality f hf hm => exact .triality f hf (hm.of_mulEquiv e)
  | ree m hm he =>
    obtain ⟨d,⟨a⟩⟩ := he
    exact .ree m hm ⟨d,⟨e.trans a⟩⟩
  | symplectic_derived hm => exact .symplectic_derived (hm.map fun a => e.trans a)
  | g2_derived hm => exact .g2_derived (hm.map fun a => e.trans a)
  | tits hm => exact .tits (hm.map fun a => e.trans a)

/-- Exhaust the full Theorem C carrier list on the original selected
container. The completed A₇, J₂ and M₂₃ rows give the original whole-W
conclusion. Only four other simple carriers, the complete binary-triality
endpoint, and the two genuine noncentral-Fitting alternatives remain. -/
theorem localCartan_escape_remaining_carriers
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    (n = 2 ∧ CartanExceptionalConclusion T L W H) ∨
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ C.Normal ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        let I := C.map (QuotientGroup.mk' (pCore 2 Y))
        A36Common I ∧
          ((K = residual H ∧ C.Normal ∧
            Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
            ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8 ∧
            n = 2 ∧ Nat.card A = 3 ∧ A ≤ C.map Y.subtype ∧
            localBorel T L ≤ omegaCentralizer T ∧
            IsOneOrTwoA5Modules L (layer L W) ∧ Nat.card B = 7 ∧
            B ≤ centralizer
              (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G)) ∨
          (IsSimpleGroup I ∧
            (Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M24) ∨
              Nonempty ((C ⧸ pCore 2 C) ≃* Held.He) ∨
              ((Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
                Nonempty ((C ⧸ pCore 2 C) ≃* Rudvalis.Model)) ∧
                K = residual H ∧
                ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
                Nat.card B = 3))) ∨
          A36Natural I ∨ A36Nilpotent I) := by
  classical
  by_cases hout : n = 2 ∧ CartanExceptionalConclusion T L W H
  · exact .inl hout
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,
    hprime,h25,hCn,hJ,hOdd,hJ4,hM22,hM23,hOddLinear,hHigher,hMathieu,hstructure⟩ :=
    localCartan_escape_seed_finiteCarriers_reduction h hH hgen c hY hescape
  let := hCn
  obtain ⟨hcommon,halt⟩ := hstructure
  refine .inr ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hCn,hKC,hlt,hn,hqlt,hcommon,?_⟩
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  let e := cComponentTwoCoreQuotientEquiv hC
  rcases halt with ⟨hs,hm⟩ | hn | hn
  · cases hm with
    | alternating m hm he =>
      have hm' : m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 := by omega
      rcases hm' with rfl | rfl | rfl | rfl
      · exact (LocalSieve.not_small_alternating_container h.qtke hKH hH.1.1.2 hKL hR
          hY hescape C hC hKC (.inl (he.map fun a => e.trans a))).elim
      · exact (LocalSieve.not_small_alternating_container h.qtke hKH hH.1.1.2 hKL hR
          hY hescape C hC hKC (.inr (.inl (he.map fun a => e.trans a)))).elim
      · exact (hout (LocalSieve.alternating_seven_cartan_exceptional h hH hgen c hKL hKT hR
          hY hescape C hC hKC (he.map fun a => e.trans a))).elim
      · exact (hHigher (.inr (.inr (he.map fun a => e.trans a)))).elim
    | linear_odd p k hp ho hk _ he => exact (hOddLinear p k hp ho hk (he.of_mulEquiv e)).elim
    | three_odd p hp ho unitary he =>
      apply False.elim
      apply hOdd p hp ho
      cases unitary
      · exact .inl (he.of_mulEquiv e)
      · exact .inr (.inl (he.of_mulEquiv e))
    | rank_one he =>
      exact (LocalSieve.not_bender_container h.qtke hKH hH.1.1.2 hKL hR
        hY hescape C hC hKC (he.of_mulEquiv e)).elim
    | rank_two he => exact .inl (hrank (rankTwo_transport e he))
    | binary_linear m hm he =>
      rcases hm with rfl | rfl
      · exact (hHigher (.inl (he.of_mulEquiv e))).elim
      · exact (hHigher (.inr (.inl (he.of_mulEquiv e)))).elim
    | sporadic name hne he =>
      cases name with
      | m11 => exact (hMathieu (.inl (he.map fun a => e.trans a))).elim
      | m12 => exact (hMathieu (.inr (he.map fun a => e.trans a))).elim
      | m22 => exact (hM22 (he.map fun a => e.trans a)).elim
      | m23 => exact (hout (LocalSieve.mathieu_twentyThree_cartan_exceptional
          h hH hgen c hKT hKL hR hY hescape C hC hKC (he.map fun a => e.trans a))).elim
      | m24 => exact .inr (.inl ⟨hs,.inl (he.map fun a => e.trans a)⟩)
      | j2 => exact (hout (LocalSieve.janko_two_cartan_exceptional h hH hgen c
          hKH hK hqs hKT hKL hR hY hescape C hC hKC (he.map fun a => e.trans a))).elim
      | j3 => exact (hne rfl).elim
      | j4 => exact (hJ4 (he.map fun a => e.trans a)).elim
      | he => exact .inr (.inl ⟨hs,.inr (.inl (he.map fun a => e.trans a))⟩)
      | hs =>
          have hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
              Nonempty ((C ⧸ pCore 2 C) ≃* Rudvalis.Model) :=
            Or.inl (he.map fun a => e.trans a)
          exact .inr (.inl ⟨hs,.inr (.inr ⟨hm,
            LocalSieve.higmanSims_rudvalis_residual_and_hall h hH hgen c hKL hKT hR
              hY hescape C hC hKC hm⟩)⟩)
      | ru =>
          have hm : Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
              Nonempty ((C ⧸ pCore 2 C) ≃* Rudvalis.Model) :=
            Or.inr (he.map fun a => e.trans a)
          exact .inr (.inl ⟨hs,.inr (.inr ⟨hm,
            LocalSieve.higmanSims_rudvalis_residual_and_hall h hH hgen c hKL hKT hR
              hY hescape C hC hKC hm⟩)⟩)
    | janko_one he => exact (hJ (he.map fun a => e.trans a)).elim
  · exact .inr (.inr (.inl hn))
  · exact .inr (.inr (.inr hn))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
