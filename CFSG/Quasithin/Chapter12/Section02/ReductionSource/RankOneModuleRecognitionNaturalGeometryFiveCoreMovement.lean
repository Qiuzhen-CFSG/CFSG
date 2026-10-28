module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFiveCoreMovement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryFiveMovement

/-!
# Core action and actual movement on the original Chapter12 witness

The same invariant cover has elementary core action and a split faithful
action image over its specified S5 quotient. Its full ambient kernel is
retained. A moving even seed involution either survives in that quotient,
or gives an actual original-Sylow core involution whose commutator with
the natural layer equals the entire Z_S.

The literal W/Z_S maps and all earlier data are unchanged. The mixed-size
premise retains its producer qt-d-tensor-mixed-size-bound. Ambient lifting,
T-invariant parabolic escape, initial 6.1.4–5, exact omega escape and final
6.1.27 assembly remain with qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith 6.1.17(4), 6.1.19, printed pp.672–675
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

/-- The original marked witness carries the full action-kernel calculation
and an actual Sylow-core displacement alternative. The mixed-size premise
is retained, and no elementary lifting premise is added. -/
theorem source_escape_ambient_five_core_movement_of_mixed_size_of_abelian
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
            NaturalFiveCoreMovementData T L (wholeReduced T L) E (P ⊔ N.pCoreIn 2) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,hcontained,hmove⟩ :=
    source_escape_ambient_five_seed_movement_of_mixed_size_of_abelian hsize D h h611 hnatural hI hab
  let := hZ
  let := hX
  let E := (commutatorLayer T L).map (MulAut.conj a).toMonoidHom
  let P := conjugateSpanBy E (Escape.I (T : Subgroup G) L (wholeReduced T L))
  let N := Escape.H (T : Subgroup G) L (wholeReduced T L)
  let K := P ⊔ N.pCoreIn 2
  have hE := source_natural_layer_hypothesisE61 D h h611 hnatural
  have hs := (source_natural_layer_rank_bounds D h h611 hnatural).2.2
  have hEK : E ≤ K := (le_conjugateSpanBy _ _).trans le_sup_left
  have hgen : conjugateSpanBy E (Escape.I (T : Subgroup G) L (wholeReduced T L)) ⊔ K.pCoreIn 2 = K := by
    rw [hcover.2.2.2.1]
  have hcore := natural_five_core_movement_data (hn ▸ h611) (hn ▸ hnatural) hE
    (by simpa [hn] using hs) a K hEK hcover.1 hcover.2.1 hescape.2.1
    ⟨hcover.2.2.2.2.1.some.trans hmodels.some⟩ hgen hab
  exact ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,
    hescape,hfive,hthree,hcontained,hmove,hcore⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
