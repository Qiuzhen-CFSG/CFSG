module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.DistanceThreeBetaKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.DistanceSource

/-!
# Source inputs for the complete distance-three Cartan kernel calculation

The genuine full local rank-one catalogue supplies Chapter 8's distance
input, and original F.1.11 supplies the source 6.5 core-intersection
obstruction. Applying both producers to the original critical configuration
retains the same fields, natural actions, full Cartan and all three kernel
exclusions. The catalogue itself remains an input; in particular this does
not eliminate its order-144 setup branch.

The separate Chapter 8 linear-quotient output at reverse pairs remains an
explicit hypothesis. Later 9.10(4)--(6), the two-natural-module splitting
and the field-two conclusion are not asserted here.
Source: DGS, *Groups and Graphs* (1985), 6.5, 8.4--8.6 and 9.10,
printed pp.121,135--139,147--150.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- Chapter 8 distance and source 6.5 are supplied by their existing producers. -/
theorem reduced_critical_distance_three_beta_kernel_of_catalogue
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
    (h8 : ∀ z : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj z a' →
      IsCriticalPair (Reduction.reducedFamily L S₀) z beta →
      ⁅Z (Reduction.reducedFamily L S₀) z,
        Z (Reduction.reducedFamily L S₀) beta⁆ = ⊥ →
      ⁅V (Reduction.reducedFamily L S₀) a' 1 ⊓
        Q (Reduction.reducedFamily L S₀) beta,
        V (Reduction.reducedFamily L S₀) beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b (Reduction.reducedFamily L S₀) = 3 ∧
          Nonempty ((graphLocalGroup (Reduction.reducedFamily L S₀) z ⧸
            pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) z)) ≃*
              SL(2,F)))
    (models : ∀ v : Vertex (Reduction.reducedFamily L S₀),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) v)))
    (Mα : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')))

 :
    let Γ := Reduction.reducedFamily L S₀
    b Γ = 3 ∧
    let H := graphLocalGroup Γ a
    let := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧
      ∃ eβ : (graphLocalGroup Γ beta ⧸
        pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F),
        (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧
        (centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) = Nat.card F ∧
        (centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) = Nat.card F ∧
        NaturalResidualSection h beta eβ n ∧
        ∃ (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (m : ℕ),
          0 < m ∧ Nat.card K = 2^m ∧
          ∃ eα : (H ⧸ pCore 2 H) ≃* SL(2,K),
            Nat.card K = Nat.card F ∧
            ⁅Q Γ beta,Z Γ a⁆ = Z Γ beta ∧ ⁅Q Γ beta,V Γ beta 1⁆ = Z Γ beta ∧
            (let q := eα.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
            let : Algebra (ZMod 2) K := ZMod.algebra K 2
            ∃ (ρ : Representation (ZMod 2) SL(2,K) (Additive (Z Γ a)))
              (T : Sylow 2 SL(2,K)),
              (∀ (l : H) (z : Additive (Z Γ a)),
                ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
                  (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) ∧
              Function.Injective ρ ∧ IsSourceNatural ρ T m ∧
              ∃ E : Additive (Z Γ a) ≃ₗ[ZMod 2] (Fin 2 → K),
                ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z)) ∧
            ∃ x : Vertex Γ, (graph Γ).Adj beta x ∧ (graph Γ).Adj x a' ∧
              ⁅V Γ beta 1,V Γ a' 1⁆ ≤ Z Γ x ∧
              V Γ beta 1 = Z Γ a ⊔ Z Γ x ∧ Nat.card (V Γ beta 1) = Nat.card F ^ 3 ∧
              V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀)) = Z Γ x ∧
              (let N := Q Γ a ⊓ Q Γ x
               N = Q Γ beta ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀)) ∧
               N ≤ Q Γ beta ∧ V Γ beta 1 ≤ N ∧
               stabilizer Γ beta ≤ normalizer (N : Set (Reduction.G₀ L S₀)) ∧
               ⁅Q Γ beta ⊓ Q Γ x,V Γ a' 1⁆ ≤ Z Γ x ∧
               ⁅N,(pResidual 2 (graphLocalGroup Γ beta)).map (graphLocalGroup Γ beta).subtype⁆ ≤ V Γ beta 1 ∧
               CoreQuotientSection Γ a beta x F eβ ∧
               N = Q Γ beta ⊓ ballKernel Γ beta 2 ∧
               (∀ z : Vertex Γ, (graph Γ).Adj beta z → N ≤ Q Γ z) ∧
               ∃ C : Subgroup (Reduction.G₀ L S₀),
                 C ≤ stabilizer Γ a ⊓ stabilizer Γ beta ⊓ stabilizer Γ x ⊓ stabilizer Γ a' ∧
                 Disjoint C ((stabilizer Γ a ⊓ stabilizer Γ beta : Subgroup (Reduction.G₀ L S₀)).pCoreIn 2) ∧
                 C ⊔ (stabilizer Γ a ⊓ stabilizer Γ beta : Subgroup (Reduction.G₀ L S₀)).pCoreIn 2 =
                   stabilizer Γ a ⊓ stabilizer Γ beta ∧
                 Odd (Nat.card C) ∧ IsMulCommutative C ∧
                 Nonempty ((C ⊓ graphLocalGroup Γ a : Subgroup (Reduction.G₀ L S₀)) ≃* Kˣ) ∧
                 Nonempty ((C ⊓ graphLocalGroup Γ beta : Subgroup (Reduction.G₀ L S₀)) ≃* Fˣ) ∧
                 C = (C ⊓ graphLocalGroup Γ a) ⊔ (C ⊓ graphLocalGroup Γ beta) ∧
                 Disjoint (C ⊓ graphLocalGroup Γ a) (C ⊓ graphLocalGroup Γ beta) ∧
                 ⁅C ⊓ graphLocalGroup Γ a,C ⊓ graphLocalGroup Γ beta⁆ = ⊥ ∧
                 (1 < n → Disjoint (C ⊓ graphLocalGroup Γ a) (ballKernel Γ a 1) ∧
                   Disjoint (C ⊓ graphLocalGroup Γ beta) (ballKernel Γ beta 1)) ∧
                 (1 < n → ∀ v : Vertex Γ, beta.type = v.type →
                   ∀ T : Subgroup (Reduction.G₀ L S₀), T ≤ graphLocalGroup Γ v →
                     Odd (Nat.card T) → T ≠ ⊥ →
                     Q Γ v ⊓ centralizer (T : Set (Reduction.G₀ L S₀)) ≤ ballKernel Γ v 2) ∧
                 (1 < n → ∀ v w : Vertex Γ, (graph Γ).Adj v w →
                   ballKernel Γ v 1 ⊓ ballKernel Γ w 1 = Q Γ v ⊓ Q Γ w) ∧
                 (1 < n → ∀ v : Vertex Γ, beta.type = v.type →
                   ∀ w : Vertex Γ, (graph Γ).Adj v w →
                     ∀ T : Subgroup (Reduction.G₀ L S₀), T ≤ graphLocalGroup Γ v →
                       Odd (Nat.card T) → Disjoint T (ballKernel Γ w 1)) ∧
                 (1 < n →
                   let T := C ⊓ graphLocalGroup Γ beta
                   let D := Q Γ beta ⊓ centralizer (T : Set (Reduction.G₀ L S₀))
                   Disjoint T (ballKernel Γ a 1) ∧ Disjoint T (ballKernel Γ x 1) ∧
                   N = V Γ beta 1 ⊔ D ∧ ⁅N,T⁆ = ⁅V Γ beta 1,T⁆ ∧
                   N = ⁅V Γ beta 1,T⁆ ⊔ D ∧ Disjoint ⁅V Γ beta 1,T⁆ D ∧
                   ⁅⁅V Γ beta 1,T⁆,D⁆ = ⊥) ∧
                 ∃ l r : Vertex Γ, (graph Γ).Adj a l ∧ l ≠ beta ∧
                   (graph Γ).Adj a' r ∧ r ≠ x ∧
                   C ≤ stabilizer Γ l ⊓ stabilizer Γ r ∧
                   Nonempty ((C ⊓ graphLocalGroup Γ l : Subgroup (Reduction.G₀ L S₀)) ≃* Fˣ) ∧
                   Nonempty ((C ⊓ graphLocalGroup Γ a' : Subgroup (Reduction.G₀ L S₀)) ≃* Fˣ) ∧
                   Nonempty ((C ⊓ graphLocalGroup Γ r : Subgroup (Reduction.G₀ L S₀)) ≃* Kˣ) ∧
                   Z Γ a = Z Γ beta ⊔ Z Γ l ∧ Disjoint (Z Γ beta) (Z Γ l) ∧
                   ¬ Z Γ l ≤ Q Γ a' ∧
                   C ⊓ graphLocalGroup Γ l ≤ ballKernel Γ a' 1 ∧
                   (1 < n →
                     let T := C ⊓ graphLocalGroup Γ l
                     let D := C ⊓ graphLocalGroup Γ a'
                     C = T ⊔ D ∧ T = C ⊓ ballKernel Γ a' 1 ∧ Disjoint T D ∧
                     Disjoint T (ballKernel Γ a 1) ∧ Disjoint T (ballKernel Γ x 1) ∧
                     Q Γ l ⊓ centralizer (T : Set (Reduction.G₀ L S₀)) ≤ ballKernel Γ l 2 ∧
                     Disjoint T (ballKernel Γ beta 1))) :=
  reduced_critical_distance_three_beta_kernel h hc hab hd hb
    (CommutingNontrivial.reduced_chapter_eight_distance_of_catalogue h models)
    hcomm htriv h8 (Reduction.reduced_graph_core_obstruction h) Mα Mβ Mα' (models a)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
