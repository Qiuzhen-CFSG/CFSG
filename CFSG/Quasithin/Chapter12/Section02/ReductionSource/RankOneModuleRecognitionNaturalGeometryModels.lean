module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryModels
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryInvolution

/-!
# Marked transvection models on the Chapter 12 reduced quotient

For each nonidentity element of the moving actor on W/Z_S, its actual
displacement orbit has the full G.6.4 classification. Restriction has kernel
exactly the centralizer of the marked element's normal closure. The original
normal closure embeds faithfully, and its isomorphism to the classified closure
is the literal restricted action map.

The Chapter 12 setup discharges all local inputs to this model construction.
Initial naturalness, the component sieve and amalgam contradiction, and final
6.1.27 assembly remain with qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, 6.1.19, pp.674–675, and G.6.4, pp.345–346.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The G.6.4 models belong to the actual reduced moving actor, with its
normal closures and conjugation maps preserved. Naturalness remains an
initial-source obligation of the unconditional 6.1.27 assembly owner. -/
theorem source_escape_reduced_transvection_models_of_abelian
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G))
    (hab : Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G)) :
    n = 2 ∧ ∃ d : NaturalEscapeGraph.OddConfiguration T L
      (normalizer (L : Set G)) (wholeReduced T L), ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L (wholeReduced T L) ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L (wholeReduced T L)
      let Z := ZS (T : Subgroup G) L (wholeReduced T L)
      let W := Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (commutatorLayer T L).map (MulAut.conj a).toMonoidHom
      let Z' := Z.map (MulAut.conj d.representative).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧ Z' ≤ W ∧ E ⊓ W = Z' ∧
      ∃ (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hN : (Z.subgroupOf W).Normal),
      let := hN
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        letI := hX
        let A := (E.subgroupOf I).map σ
        let J := (P.subgroupOf I).map σ
        let θ : Representation (ZMod 2) J (Additive (W ⧸ Z.subgroupOf W)) :=
          Representation.ofElementaryAbelianAction
          (A := J) (G := W ⧸ Z.subgroupOf W) (p := 2)
        IsElementaryAbelian 2 A ∧ 1 < Nat.card A ∧ Nat.card A ≤ 4 ∧
        commutatorAction A (W ⧸ Z.subgroupOf W) =
          (Z'.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W)) ∧
        Nat.card ((Z'.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W))) = 2 ∧
        commutatorAction₂ A (W ⧸ Z.subgroupOf W) = ⊥ ∧
        σ.ker = (commutatorPreimage I W Z).subgroupOf I ∧
        J = conjugateSpanBy A σ.range ∧ pCore 2 J = ⊥ ∧
        ChapterB.SourceInduction.FFHypothesis KnownSimple.IsKnownSimple θ ∧
        ChapterB.SourceInduction.NontrivialAdequateAlternative θ ∧
        ∀ t : J, (t : MulAut (W ⧸ Z.subgroupOf W)) ∈ A → t ≠ 1 →
          Module.finrank (ZMod 2) (LinearMap.range
            (θ t - LinearMap.id (R := ZMod 2) (M := Additive (W ⧸ Z.subgroupOf W)))) = 1 ∧
          Nonempty (TransvectionOrbitModel θ t) := by
  obtain ⟨d⟩ := source_escape_odd_configuration_of_abelian D h h611 hnatural hI hab
  obtain ⟨hn,ht⟩ := d.exists_reduced_transvection_models h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611) hab
  exact ⟨hn,d,ht⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
