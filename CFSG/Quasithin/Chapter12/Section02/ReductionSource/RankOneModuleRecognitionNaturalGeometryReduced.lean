module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryReduced
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryInvolution

/-!
# The reduced odd transvection action on the Chapter 12 layer

The actual odd configuration gives a faithful normal-closure image on
W/Z_S with trivial two-core, preserving the moving elementary actor of
order two or four and its order-two displacement line. The explicit image
surjection has kernel exactly the original image’s two-core. Passing from
W/<z> to W/Z_S uses the proved core bound with its original denominator.

The component/amalgam contradiction, initial naturalness and final
6.1.27 assembly remain with qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, 6.1.19, printed pp.674–675.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The reduced transvection normal closure on W/Z_S, with the Chapter 12
configuration inputs discharged and the literal quotient action retained. -/
theorem source_escape_reduced_transvection_action_of_abelian
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
        IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W) ∧
        let A := (E.subgroupOf I).map σ
        let J := (P.subgroupOf I).map σ
        IsElementaryAbelian 2 A ∧ 1 < Nat.card A ∧ Nat.card A ≤ 4 ∧
        commutatorAction A (W ⧸ Z.subgroupOf W) =
          (Z'.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W)) ∧
        Nat.card ((Z'.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W))) = 2 ∧
        commutatorAction₂ A (W ⧸ Z.subgroupOf W) = ⊥ ∧
        σ.ker = (commutatorPreimage I W Z).subgroupOf I ∧
        J = conjugateSpanBy A σ.range ∧ pCore 2 J = ⊥ ∧
        ∃ hD : ((zpowers z).subgroupOf W).Normal,
          letI := hD
          ∃ ρ : I →* MulAut (W ⧸ (zpowers z).subgroupOf W),
            (∀ i : I, ∀ w : W,
              ρ i (QuotientGroup.mk' ((zpowers z).subgroupOf W) w) =
                QuotientGroup.mk' ((zpowers z).subgroupOf W)
                  ⟨(i : G) * (w : G) * (i : G)⁻¹,
                    (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
            ∃ hPI : P ≤ I,
              let f := ρ.comp (inclusion hPI)
              let g := σ.comp (inclusion hPI)
              ∃ β : f.range →* g.range, Function.Surjective β ∧
                (∀ p, β (f.rangeRestrict p) = g.rangeRestrict p) ∧
                β.ker = pCore 2 f.range := by
  obtain ⟨d⟩ := source_escape_odd_configuration_of_abelian D h h611 hnatural hI hab
  obtain ⟨hn,ht⟩ := d.exists_reduced_transvection_action h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611) hab
  exact ⟨hn,d,ht⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
