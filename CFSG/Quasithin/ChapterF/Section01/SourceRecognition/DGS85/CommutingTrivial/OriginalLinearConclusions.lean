module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.OriginalLinearApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.LinearApplications

/-!
# Small-neighbor conclusions from original linear source rows

The original F.1.11 linear rows now provide the actual graph quotient
markings and the universal adjacent-edge 6.5 obstruction.  This module feeds
those witnesses directly into the existing small-neighbor consumer, retaining
the two literal fields and their source cardinality parameters.
-/

@[expose] public noncomputable section
open Subgroup
open Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- Original linear quotient rows discharge the supplied-marking and 6.5
premises of the small-neighbor linear conclusion theorem. -/
theorem reduced_small_neighbor_linear_conclusions_of_original_models
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓
      Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (hs : V (Reduction.reducedFamily L S₀) a' 1 ≤
      Q (Reduction.reducedFamily L S₀) beta)
    (hm : ∀ i : Bool, ∃ n : ℕ,
      0 < n ∧ ClassicalGroup.IsPSL
        (family L i ⧸ pCore 2 (family L i)) 2 (2 ^ n)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (n m : ℕ),
      0 < n ∧ Nat.card F = 2 ^ n ∧
      0 < m ∧ Nat.card K = 2 ^ m ∧
      ∃ eα : (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)) ≃* SL(2, F),
        ∃ _eβ : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
          pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2, K),
          let Γ := Reduction.reducedFamily L S₀
          let H := graphLocalGroup Γ a
          let q := eα.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
          letI := Z_elementary Γ (fun v => (source_Z_Q_U
            (Reduction.reduced_triple h) v).1) a
          letI : Algebra (ZMod 2) F := ZMod.algebra F 2
          Nat.card F = Nat.card K ∧
            (Q Γ a).relIndex (V Γ a' 1) = Nat.card F ∧
            (Q Γ a').relIndex (Z Γ a) = Nat.card F ∧
            (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧
            ⁅Q Γ beta, Z Γ a⁆ = Z Γ beta ∧
            ⁅V Γ beta 1, Q Γ beta⁆ = Z Γ beta ∧
            ∃ (ρ : Representation (ZMod 2) SL(2,F) (Additive (Z Γ a)))
              (T : Sylow 2 SL(2,F)),
              (∀ (l : H) (z : Additive (Z Γ a)),
                ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
                  (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) ∧
              Function.Injective ρ ∧ IsSourceNatural ρ T n ∧
              ∃ E : Additive (Z Γ a) ≃ₗ[ZMod 2] (Fin 2 → F),
                ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z) := by
  obtain ⟨F, hF, hFfin, hFchar, K, hK, hKfin, hKchar, n, m,
      hn, hFcard, hmpos, hKcard, eα, eβ, _⟩ :=
    reduced_small_neighbor_linear_inputs_of_original_models h (a := a) (beta := beta) hm
  exact ⟨F, hF, hFfin, hFchar, K, hK, hKfin, hKchar, n, m,
    hn, hFcard, hmpos, hKcard, eα, eβ,
    reduced_small_neighbor_linear_conclusions h hc hab hd hb hcomm htriv hs
      hn hFcard hmpos hKcard eα eβ⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
