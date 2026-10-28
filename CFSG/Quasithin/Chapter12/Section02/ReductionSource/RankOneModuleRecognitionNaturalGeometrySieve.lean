module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometrySieve
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryInvolution

/-!
# The small-factor sieve on the Chapter 12 central-line quotient

For the actual action on W/Z_S, the ambient component lifts exclude all
large G.6.4 rows. Every subnormal classified factor has the marked binary
natural action of degree two or three, or the natural S₅ action. In the
first case its two-residual has order three. In the other cases the literal
two-residual equals the solvable residual and lifts to an ambient component
with the same simple central quotient. Both original quotient maps and the
ambient inclusion are retained. The component lifts are identified with the
residuals of the literal factor preimages and are normalized by every cubic
in the original ambient normalizer quotient.

This discharges the component-sieve premise for classified factors of this
image. Existence and assembly of a complete compatible factor family,
normalization of the full factors by the original cubic, the parabolic/amalgam contradiction,
initial 6.1.4–5 and unconditional 6.1.27 remain with
qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith 6.1.19, printed pp.674–675.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Every classified factor of the literal reduced image passes the source
sieve; its actual residual is either cubic or lifts to an ambient component. -/
theorem source_escape_ambient_reduced_small_factor_lifts_of_abelian
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
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        letI := hX
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
          let θ := Representation.ofElementaryAbelianAction
            (A := g.range) (G := W ⧸ Z.subgroupOf W) (p := 2)
          ∀ (K : Subgroup g.range), K.IsSubnormal →
            ∀ U : Submodule (ZMod 2) (Additive (W ⧸ Z.subgroupOf W)),
              ChapterG.Section06.FactorModel θ K U →
              ChapterG.Section06.SmallFactorModel θ K U ∧
                ((Nonempty (K ≃* Equiv.Perm (Fin 3)) ∧ Nat.card (pResidual 2 K) = 3) ∨
                 (let D := (solvableResidual K).map K.subtype
                  (pResidual 2 K).map K.subtype = D ∧
                  ∃ C : Subgroup (P ⧸ pCore 2 P),
                    C = (solvableResidual (K.comap φ)).map (K.comap φ).subtype ∧
                    IsComponent _ C ∧ C.map φ = D ∧
                    IsComponent (N ⧸ pCore 2 N) (C.map j) ∧
                    Nonempty (((C.map j) ⧸ center (C.map j)) ≃* (D ⧸ center D)) ∧
                    C.map j ≤ (I.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)) ∧
                    (∀ c : N ⧸ pCore 2 N, c ^ 3 = 1 →
                      c ∈ Subgroup.normalizer (C.map j : Set (N ⧸ pCore 2 N))) ∧
                    (Nonempty ((D ⧸ center D) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
                     Nonempty ((D ⧸ center D) ≃* alternatingGroup (Fin 5))))) := by
  obtain ⟨d⟩ := source_escape_odd_configuration_of_abelian D h h611 hnatural hI hab
  exact d.exists_ambient_reduced_small_factor_lifts h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611) hab

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
