module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFiveCubicCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryFiveCoreMovement

/-!
# Cubic orbit covers on the original Chapter12 witness

The original core-moving involution now generates, with its two cubic
conjugates, an actual invariant two-subgroup inside the original Sylow.
Its action on the natural-layer span is elementary of order four. The
cubic norm belongs to the full ambient centralizer kernel, which is
retained explicitly. The orbit subgroup itself is not asserted elementary.

All original W/Z_S maps, quotient markings and prior alternatives are
preserved. The mixed-size premise keeps qt-d-tensor-mixed-size-bound as
its producer. Elementary lifting for S5, canonical parabolic escape,
initial 6.1.4–5, exact omega escape and unconditional 6.1.27 remain with
qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith 6.1.17(4), 6.1.19, pp.672–675
(`refs/quasithin.pdf`).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped IsMulCommutative Classical
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The same original witness retains the actual cubic orbit cover of
every full-line core mover, with its complete centralizer kernel. The
mixed-size premise remains explicit. -/
theorem source_escape_ambient_five_cubic_core_of_mixed_size_of_abelian
    (hsize : NaturalMixedSizeInput G)
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G))
    (hab : Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L (wholeReduced T L) ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L (wholeReduced T L)
      let N := Escape.H (T : Subgroup G) L (wholeReduced T L)
      let Z := ZS (T : Subgroup G) L (wholeReduced T L)
      let W := Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (commutatorLayer T L).map (MulAut.conj a).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧
      ∃ (hPI : P ≤ I) (hPN : P ≤ N) (_hIN : I ≤ N)
        (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hZ : (Z.subgroupOf W).Normal),
      letI := hZ
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        letI := hX
        IsElementaryAbelian 2 ((E.subgroupOf I).map σ) ∧
        1 < Nat.card ((E.subgroupOf I).map σ) ∧
        Nat.card ((E.subgroupOf I).map σ) ≤ 4 ∧
        let g := σ.comp (inclusion hPI)
        ∃ (φ : (P ⧸ pCore 2 P) →* g.range)
          (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N)),
          Function.Bijective φ ∧ φ.ker ≤ center (P ⧸ pCore 2 P) ∧
          Function.Injective j ∧ j.range.IsSubnormal ∧
          (∀ p, φ (QuotientGroup.mk' (pCore 2 P) p) = g.rangeRestrict p) ∧
          (∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
            QuotientGroup.mk' (pCore 2 N) (inclusion hPN p)) ∧
          pCore 2 g.range = ⊥ ∧ g.ker = pCore 2 P ∧
            Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 5)) ∧
            ((pResidual 2 P).map P.subtype = (primeToResidual 3 I).map I.subtype) ∧
            (N ≤ Subgroup.normalizer ((pResidual 2 P).map P.subtype : Set G)) ∧
            NaturalInvariantCoverData T P I N σ hPI ∧
            NaturalEscapingCoverData T P N (normalizer (L : Set G)) ∧
            NaturalFiveCubicParabolicData T L (wholeReduced T L) P N ∧
            NaturalThreeInvariantParabolicData T L (wholeReduced T L) P N (normalizer (L : Set G)) ∧
            (NaturalFiveContainedParabolicData T P N (normalizer (L : Set G)) ∧
                NaturalFiveElementaryRestriction P N ∧
                NaturalFiveCubicFixedData T L (wholeReduced T L) P N ∧
                NaturalFiveSpanActionData T L (wholeReduced T L) (P ⊔ N.pCoreIn 2) ∧
                NaturalFiveFixedOrbitData T L (wholeReduced T L) (P ⊔ N.pCoreIn 2) (normalizer (L : Set G)) ∧
                NaturalFiveSpanSeparationData T L (wholeReduced T L) (P ⊔ N.pCoreIn 2) ∧
                NaturalFiveSpanRetractionData T L (wholeReduced T L) (P ⊔ N.pCoreIn 2) ∧
                NaturalFiveSeedEscapeData T L E P N (normalizer (L : Set G)) ∧
                NaturalFiveSeedNormalizerData T L P N (normalizer (L : Set G)) ∧
                ∃ c t : G, c ∈ L ∧ c ∈ N ∧ orderOf c=3 ∧
                  t ∈ N.pCoreIn 2 ∧ orderOf t=2 ∧ c*t*c⁻¹=t ∧ t ∉ Z ∧ t ∉ conjugateSpanBy (commutatorLayer T L) (P ⊔ N.pCoreIn 2) ∧
                  t ∈ centralizer (commutatorLayer T L : Set G) ∧
                  t ∈ centralizer (conjugateSpanBy (commutatorLayer T L)
                    ((P ⊔ N.pCoreIn 2) ⊓ centralizer (zpowers c : Set G)) : Set G)) ∧
            NaturalFiveSeedMovementData T L (wholeReduced T L) E (P ⊔ N.pCoreIn 2) ∧
            NaturalFiveCoreMovementData T L (wholeReduced T L) E (P ⊔ N.pCoreIn 2) ∧
            NaturalFiveCubicCoreData T L (wholeReduced T L) E (P ⊔ N.pCoreIn 2) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,hcontained,hmove,hcore⟩ :=
    source_escape_ambient_five_core_movement_of_mixed_size_of_abelian hsize D h h611 hnatural hI hab
  let := hZ
  let := hX
  let E := (commutatorLayer T L).map (MulAut.conj a).toMonoidHom
  let P := conjugateSpanBy E (Escape.I (T : Subgroup G) L (wholeReduced T L))
  let N := Escape.H (T : Subgroup G) L (wholeReduced T L)
  let K := P ⊔ N.pCoreIn 2
  have hE := source_natural_layer_hypothesisE61 D h h611 hnatural
  have hcubic := natural_five_cubic_core_data (hn ▸ h611) (hn ▸ hnatural) hE
    K hcover.1 hcover.2.1 hescape.2.1
    E hcore hab
  exact ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,
    hescape,hfive,hthree,hcontained,hmove,hcore,hcubic⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
