module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryJankoExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryMixedCubic

/-!
# Hall--Janko exclusions on the original Chapter12 witness

The natural layer of order sixteen lies in the full left two-core. The
concrete ordinary and automorphism Hall--Janko first cores have order 32
and contain Q8, so neither can contain this elementary layer. Solvability
of the original right parabolic excludes the reversed orientations.
The source application uses the same W/Z_S witness and escaping subgroup,
retaining all original quotient maps, kernels, cubic constraints and the
contained S5 alternative.

The remaining mixed recognition must construct an actual model from the
source pair. It is not supplied by these model exclusions. S5 parabolic
escape, initial 6.1.4–5, omega escape and the remaining geometry through
unconditional 6.1.27 remain with qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith 6.1.19, printed p.675, and F.1.12(I)(10–11),
printed p.263 (`refs/quasithin.pdf`).
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

/-- Exclude both concrete Hall--Janko rows in both orientations on the
same escaping pair and original W/Z_S witness. -/
theorem source_escape_ambient_amalgam_or_five_janko_exclusion_of_abelian
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
            (Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 5))) ∧
            ((pResidual 2 P).map P.subtype = (primeToResidual 3 I).map I.subtype) ∧
            (N ≤ Subgroup.normalizer ((pResidual 2 P).map P.subtype : Set G)) ∧
            NaturalInvariantCoverData T P I N σ hPI ∧
            NaturalEscapingCoverData T P N (normalizer (L : Set G)) ∧
            NaturalFiveCubicParabolicData T L (wholeReduced T L) P N ∧
            NaturalThreeInvariantParabolicData T L (wholeReduced T L) P N (normalizer (L : Set G)) ∧
            (NaturalEscapingAmalgamJankoData T L (wholeReduced T L) P N (normalizer (L : Set G)) ∨
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
                    ((P ⊔ N.pCoreIn 2) ⊓ centralizer (zpowers c : Set G)) : Set G))) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,ham⟩ :=
    source_escape_ambient_amalgam_or_five_right_cubic_of_abelian D h h611 hnatural hI hab
  let := hZ
  let := hX
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,?_⟩
  exact ham.imp_left (natural_escaping_amalgam_janko_exclusion (hn ▸ h611) (hn ▸ hnatural))

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
