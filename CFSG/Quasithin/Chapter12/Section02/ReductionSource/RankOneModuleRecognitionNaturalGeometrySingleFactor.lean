module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometrySingleFactor
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryInvolution

/-!
# The single marked factor on the Chapter 12 reduced layer

The original cubic outside the centralizer image normalizes every quotient
factor. Conjugation orbit counting and three-rank at most two exclude two
independent commuting factors. Thus the sole marked factor is the whole
W/Z_S action image, its literal preimage is P, and the original quotient
P/O₂(P) is isomorphic to S₃, L₃(2), or S₅. The ambient two-core lies in I and normalizes P, so cubic normalization
also lifts to the original O²(P). Both covering maps, their equations,
the module marking and the earlier normalization statements are retained.

This discharges the single-factor step of Aschbacher–Smith 6.1.19, printed
p.675, on the original Chapter 12 witness. The parabolic/amalgam contradiction,
initial 6.1.4–5, omega escape and the remaining geometry are still owned by
qt-d-1222-rankone-recognition-natural, which must discharge the hypotheses
and assemble unconditional 6.1.27.
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

/-- The original escape action has one full marked factor, whose literal
preimage is P and whose model identifies P/O₂(P). -/
theorem source_escape_ambient_single_factor_of_abelian
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
      ∃ (hPI : P ≤ I) (hPN : P ≤ N) (hIN : I ≤ N)
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
          closure {x : P ⧸ pCore 2 P | x ^ 2 = 1} = ⊤ ∧
          let θ := Representation.ofElementaryAbelianAction
            (A := g.range) (G := W ⧸ Z.subgroupOf W) (p := 2)
          ∃ product : SmallTransvectionProductModel θ,
            product.factors = {⊤} ∧
            (∃ U : Submodule (ZMod 2) (Additive (W ⧸ Z.subgroupOf W)),
              CFSG.Quasithin.ChapterG.Section06.SmallFactorModel θ ⊤ U) ∧
            (Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 5))) ∧
            (∀ c : N, c^3=1 → (c : G) ∈ Subgroup.normalizer
              ((pResidual 2 P).map P.subtype : Set G)) ∧
            (∀ K ∈ product.factors,
              (((K.comap φ).comap (QuotientGroup.mk' (pCore 2 P))).map P.subtype) = P) ∧
            (∀ K ∈ product.factors, FactorResidualLift φ j
              ((I.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))) K ∧
              ∀ c : N ⧸ pCore 2 N, c^3=1 →
                c ∈ normalizer ((((pResidual 2 (K.comap φ)).map
                  (K.comap φ).subtype).map j) : Set (N ⧸ pCore 2 N))) ∧
            (∀ K ∈ product.factors,
              ((pResidual 2 I).map (inclusion hIN)).map (QuotientGroup.mk' (pCore 2 N)) ≤
                normalizer ((K.comap φ).map j : Set (N ⧸ pCore 2 N)) ∧
              (pResidual 2 I).map I.subtype ≤ normalizer
                ((((K.comap φ).comap (QuotientGroup.mk' (pCore 2 P))).map P.subtype) : Set G)) ∧
            (∀ K ∈ product.factors, ∀ c : N ⧸ pCore 2 N, c^3=1 →
              c ∈ normalizer ((K.comap φ).map j : Set (N ⧸ pCore 2 N))) ∧
            (∀ c : N ⧸ pCore 2 N, c^3=1 →
              c ∈ normalizer (j.range : Set (N ⧸ pCore 2 N))) ∧
            (∀ K ∈ product.factors, ∀ c : N, c^3=1 →
              c ∈ normalizer (((K.comap φ).map j).comap
                (QuotientGroup.mk' (pCore 2 N)) : Set N)) ∧
            ∃ e : (∀ K : {K // K ∈ product.factors}, K.val) ≃* (P ⧸ pCore 2 P),
              (∀ x, φ (e x) = product.productEquiv x) ∧
              (∀ K : {K // K ∈ product.factors}, ∀ a : P ⧸ pCore 2 P,
                a ∈ K.val.comap φ ↔ ∃ x : K.val,
                  e (Function.update 1 K x) = a) := by
  obtain ⟨d⟩ := source_escape_odd_configuration_of_abelian D h h611 hnatural hI hab
  exact d.exists_ambient_single_factor h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611) hab

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
