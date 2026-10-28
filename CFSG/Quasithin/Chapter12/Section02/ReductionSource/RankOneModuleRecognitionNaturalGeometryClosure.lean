module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryClosure
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryInvolution

/-!
# The odd normal-closure action on the Chapter 12 reduced layer

The actual odd critical configuration supplies the moving transvection
actor on (U intersect Q_z)/<z>. The core-image comparison now identifies
O₂(P*) with O₂(P)*, and the order-two endpoint intersection embeds that
nontrivial actor into P*/O₂(P*).

The vanishing of this image core, subsequent component and amalgam
contradiction, initial naturalness and final 6.1.27 assembly remain with
qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, 6.1.19, printed pp.674–675.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The normal-closure core comparison and surviving actor under the contrary
abelian assumption, with the Chapter 12 configuration inputs discharged. -/
theorem source_escape_involution_closure_action_of_abelian
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
      let W := Escape.U (T : Subgroup G) L (wholeReduced T L) ⊓
        conjugateSpanBy (ZS (T : Subgroup G) L (wholeReduced T L)) (centralizer ({z} : Set G))
      let E := (commutatorLayer T L).map (MulAut.conj a).toMonoidHom
      let Z' := (ZS (T : Subgroup G) L (wholeReduced T L)).map (MulAut.conj d.representative).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z' ≤ W ∧ E ⊓ W = Z' ∧
      ∃ (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hN : ((zpowers z).subgroupOf W).Normal),
      letI := hN
      ∃ ρ : I →* MulAut (W ⧸ (zpowers z).subgroupOf W),
        (∀ i : I, ∀ w : W,
          ρ i (QuotientGroup.mk' ((zpowers z).subgroupOf W) w) =
            QuotientGroup.mk' ((zpowers z).subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
        IsElementaryAbelian 2 (W ⧸ (zpowers z).subgroupOf W) ∧
        let A := (E.subgroupOf I).map ρ
        let J := (P.subgroupOf I).map ρ
        IsElementaryAbelian 2 ((E.subgroupOf I).map ρ) ∧
        1 < Nat.card ((E.subgroupOf I).map ρ) ∧
        Nat.card ((E.subgroupOf I).map ρ) ≤ 4 ∧
        commutatorAction ((E.subgroupOf I).map ρ) (W ⧸ (zpowers z).subgroupOf W) =
          (Z'.subgroupOf W).map (QuotientGroup.mk' ((zpowers z).subgroupOf W)) ∧
        Nat.card ((Z'.subgroupOf W).map (QuotientGroup.mk' ((zpowers z).subgroupOf W))) = 2 ∧
        commutatorAction₂ ((E.subgroupOf I).map ρ) (W ⧸ (zpowers z).subgroupOf W) = ⊥ ∧
        ρ.ker = (commutatorPreimage I W (zpowers z)).subgroupOf I ∧
        J = conjugateSpanBy A ρ.range ∧
        ((P.pCoreIn 2).subgroupOf I).map ρ = J.pCoreIn 2 ∧
        A ⊓ J.pCoreIn 2 = ⊥ ∧
        ∃ hAJ : A ≤ J,
          Function.Injective ((QuotientGroup.mk' (pCore 2 J)).comp (inclusion hAJ)) := by
  obtain ⟨d⟩ := source_escape_odd_configuration_of_abelian D h h611 hnatural hI hab
  obtain ⟨hn,ht⟩ := d.exists_involution_closure_action h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611) hab
  exact ⟨hn,d,ht⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
