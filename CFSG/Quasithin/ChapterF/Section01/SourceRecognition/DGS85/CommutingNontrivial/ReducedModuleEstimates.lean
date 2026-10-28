module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.IndexEstimates

/-!
# Literal reduced-F1.11 application of the moving-center estimates

The original nonzero H selects a moving neighbor in the reduced source
graph. The constructed earlier-local data discharge full-kernel Sylow
control, the center dichotomy and actual Sylow-fixed generation. On this
same neighbor the source core indices satisfy the linear lower bound and
conditional natural recognition, or the Suzuki and large-unitary square
bounds. All original quotient representative formulas remain explicit.

Only the original F1.11 assumptions and the earlier 6.5 obstruction are
used to construct the source data; actual model isomorphisms remain the
6.1 inputs. No faithful-module or fixed-generation input remains in these
estimates. The two small unitary rows, D₁₀, the quotient-center action and
8.2--8.7 are not asserted here and remain with this Chapter 8 owner.

Source: DGS, *Groups and Graphs* (1985), 8.0--8.7, pp.132--140,
with corrected 5.12 and the original/reduced conventions of F1.9.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type*} [Group G]

/-- Every actual Suzuki marking of the selected reduced neighbor satisfies
the square bound, including Sz(2). -/
theorem reduced_moving_suzuki_index_bound
    {J : Fin 2 → Subgroup G} {S₀ : Subgroup G} (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a, Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    (m : ℕ) :
    let F := Reduction.reducedFamily J S₀
    let A := V F beta 1 ⊓ Q F a'
    ∃ w : (graph F).neighborSet a',
      ⁅A, Z F w.val⁆ ≠ ⊥ ∧
      ∀ _e : (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) ≃* SuzukiMatrixGroup m,
        (Q F w.val).relIndex A ^ 2 ≤
          (centralizer (A : Set (Reduction.G₀ J S₀))).relIndex (Z F w.val) := by
  dsimp only
  let h' := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  obtain ⟨w, hm, _⟩ := exists_moving_neighbor (Reduction.reducedFamily J S₀)
    (fun v => (source_Z_Q_U h' v).1) beta a' hne
  exact ⟨w, hm, fun e => source_moving_suzuki_index_bound h' d hc hab hd hb hcomm w hm m e⟩

/-- The same reduced moving neighbor satisfies both unitary index estimates
at field order at least four, retaining the special and projective maps. -/
theorem reduced_moving_unitary_index_bounds
    {J : Fin 2 → Subgroup G} {S₀ : Subgroup G} (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a, Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    {K : Type u} [Field K] [Finite K] (M : HermitianForm 3 K)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, M.conj x = x^(2^n)) :
    let F := Reduction.reducedFamily J S₀
    let A := V F beta 1 ⊓ Q F a'
    ∃ w : (graph F).neighborSet a',
      ⁅A, Z F w.val⁆ ≠ ⊥ ∧
      (∀ _e : (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) ≃* M.specialSubgroup,
        (Q F w.val).relIndex A ^ 2 ≤
          (centralizer (A : Set (Reduction.G₀ J S₀))).relIndex (Z F w.val)) ∧
      (∀ _e : (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) ≃*
          ProjectiveSpecialUnitaryMatrixGroup M,
        (Q F w.val).relIndex A ^ 2 ≤
          (centralizer (A : Set (Reduction.G₀ J S₀))).relIndex (Z F w.val)) := by
  dsimp only
  let h' := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  obtain ⟨w, hm, _⟩ := exists_moving_neighbor (Reduction.reducedFamily J S₀)
    (fun v => (source_Z_Q_U h' v).1) beta a' hne
  exact ⟨w, hm,
    fun e => source_moving_special_unitary_index_bound h' d hc hab hd hb hcomm w hm M hn hK hconj e,
    fun e => source_moving_projective_unitary_index_bound h' d hc hab hd hb hcomm w hm M hn hK hconj e⟩

/-- The literal reduced linear model has a faithful natural realization
once the source strict index inequality is established. The chosen moving
neighbor, quotient representatives and vectors are retained. -/
theorem reduced_moving_linear_recognition
    {J : Fin 2 → Subgroup G} {S₀ : Subgroup G} (h : HypothesisF11 J S₀)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S₀),
      (graph (Reduction.reducedFamily J S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S₀) w ⊓ Q (Reduction.reducedFamily J S₀) v :
          Subgroup (Reduction.G₀ J S₀)) : Set (Reduction.G₀ J S₀)))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a, Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2^n) :
    let F := Reduction.reducedFamily J S₀
    letI : ∀ v : Vertex F, IsElementaryAbelian 2 (Z F v) :=
      fun v => CommutingOneProfile.source_center_elementary (Reduction.reduced_triple h) v
    let A := V F beta 1 ⊓ Q F a'
    ∃ w : (graph F).neighborSet a',
      ⁅A, Z F w.val⁆ ≠ ⊥ ∧
      ∀ e : (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) ≃* SL(2,K),
        (Q F w.val).relIndex A ≤
          (centralizer (A : Set (Reduction.G₀ J S₀))).relIndex (Z F w.val) ∧
        ((centralizer (A : Set (Reduction.G₀ J S₀))).relIndex (Z F w.val) <
          (Q F w.val).relIndex A ^ 2 →
        ∃ (ρ : Representation (ZMod 2) SL(2,K) (Additive (Z F w.val))) (S : Sylow 2 SL(2,K)),
          (∀ (l : graphLocalGroup F w.val) (z : Additive (Z F w.val)),
            ((ρ (e (QuotientGroup.mk' (pCore 2 (graphLocalGroup F w.val)) l)) z).toMul :
                Reduction.G₀ J S₀) =
              (l : Reduction.G₀ J S₀) * z.toMul * (l : Reduction.G₀ J S₀)⁻¹) ∧
          Function.Injective ρ ∧ NaturalRealization ρ S) := by
  let : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsElementaryAbelian 2 (Z (Reduction.reducedFamily J S₀) v) :=
    fun v => CommutingOneProfile.source_center_elementary (Reduction.reduced_triple h) v
  dsimp only
  let h' := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  obtain ⟨w, hm, _⟩ := exists_moving_neighbor (Reduction.reducedFamily J S₀)
    (fun v => (source_Z_Q_U h' v).1) beta a' hne
  exact ⟨w, hm, fun e =>
    source_moving_linear_index_recognition h' d hc hab hd hb hcomm w hm hn hK e⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
