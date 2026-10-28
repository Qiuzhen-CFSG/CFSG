module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryLift
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryInvolution

/-!
# Component lifts from the Chapter 12 central-line quotient

The original odd escaping configuration constructs a nontrivial moving actor
on W/Z_S. Its actual image is covered centrally by P/O₂(P), and the latter
embeds subnormally in N_G(Z_S)/O₂(N_G(Z_S)), retaining the quotient maps.
Ordinary components of this reduced image therefore lift to components of
that ambient quotient, with the same simple central quotients. The original
cubic excludes alternating degree at least six and binary degrees four and
five for those quotients, including all possible central covers.

This application discharges the E.6, rank and Sylow-normalizer premises using
the chosen Chapter 12 module. Initial naturalness, factor selection and
assembly, the amalgam contradiction and unconditional 6.1.27 remain with
qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith 6.1.19, printed pp.674–675.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The actual reduced image has a central cover in the normalizer quotient;
its components lift and satisfy the source cubic exclusions. Naturalness
remains an earlier-source premise of the final 6.1.27 owner. -/
theorem source_escape_ambient_reduced_component_lifts_of_abelian
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
      ∃ (hPI : P ≤ I) (hPN : P ≤ N)
        (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hZ : (Z.subgroupOf W).Normal),
      letI := hZ
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
        IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W) ∧
        IsElementaryAbelian 2 ((E.subgroupOf I).map σ) ∧
        1 < Nat.card ((E.subgroupOf I).map σ) ∧
        Nat.card ((E.subgroupOf I).map σ) ≤ 4 ∧
        let g := σ.comp (inclusion hPI)
        ∃ (φ : (P ⧸ pCore 2 P) →* g.range)
          (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N)),
          Function.Surjective φ ∧ φ.ker ≤ center (P ⧸ pCore 2 P) ∧
          Function.Injective j ∧ j.range.IsSubnormal ∧
          (∀ p, φ (QuotientGroup.mk' (pCore 2 P) p) = g.rangeRestrict p) ∧
          (∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
            QuotientGroup.mk' (pCore 2 N) (inclusion hPN p)) ∧
          pCore 2 g.range = ⊥ ∧
          ∀ D : Subgroup g.range, IsComponent g.range D →
            ∃ C : Subgroup (P ⧸ pCore 2 P), IsComponent _ C ∧ C.map φ = D ∧
              IsComponent (N ⧸ pCore 2 N) (C.map j) ∧
              Nonempty (((C.map j) ⧸ center (C.map j)) ≃* (D ⧸ center D)) ∧
              C.map j ≤ (I.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)) ∧
              (∀ m, 6 ≤ m → ¬ Nonempty ((D ⧸ center D) ≃* alternatingGroup (Fin m))) ∧
              (∀ m, m = 4 ∨ m = 5 →
                ¬ Nonempty ((D ⧸ center D) ≃* BinaryLinear.OuterCyclic.LinearGroup m)) := by
  obtain ⟨d⟩ := source_escape_odd_configuration_of_abelian D h h611 hnatural hI hab
  exact d.exists_ambient_reduced_component_lifts h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611) hab

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
