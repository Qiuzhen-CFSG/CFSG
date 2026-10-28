module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.NeighborCenterCentralizer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.NeighborEscapeApplication

/-!
# The binary 6.5 escape configuration without a noncentrality premise

The proved field-of-two central-case exclusion discharges noncentrality
in the original reduced F1.11 escape theorem. The resulting neighboring
center escapes the actual closure core. With the other endpoint's original
linear quotient, an odd-order element transports the original neighbor to
this one and moves the closure core, retaining the inclusion in the original
enlarged endpoint and the original full Borel used to construct it.

No equality of the two fields is imposed. The remaining Frattini and
two-maximal-subgroup contradiction is not a hypothesis or an asserted result.
Source: DGS, Groups and Graphs (1985), 6.5, pp.121–122.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The original binary quotient supplies an escaping neighbor, with its central alternative discharged. -/
theorem reduced_binary_escaping_neighbor (h : HypothesisF11 L S) (j : Bool)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data
      (other (if j then 1 else 0)))) ≤ normalizer
      (↑(((P₀ L S (if j then 1 else 0)).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other (if j then 1 else 0))).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)))
    (e : (L (other (if j then 1 else 0)) ⧸ pCore 2 (L (other (if j then 1 else 0)))) ≃* PSL(2,F))
    (hF : Nat.card F = 2) :
    let X := conjugateSpanBy (Q (reducedFamily L S) (base (reducedFamily L S) j))
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!j)))
    (¬ V (reducedFamily L S) (base (reducedFamily L S) j) 1 ≤ X.pCoreIn 2) ∧
    ∃ mu : Vertex (reducedFamily L S), (graph (reducedFamily L S)).Adj (base (reducedFamily L S) j) mu ∧
      Z (reducedFamily L S) mu ≤ Q (reducedFamily L S) (base (reducedFamily L S) j) ∧
      ¬ Z (reducedFamily L S) mu ≤ X.pCoreIn 2 := by
  have hnc : ¬ Z (reducedFamily L S) (base (reducedFamily L S) (!j)) ≤ centralizer
      (conjugateSpanBy (Q (reducedFamily L S) (base (reducedFamily L S) j))
        (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!j))) : Set (G₀ L S)) := by
    simp only [Z,Q,stabilizer,Subgroup.CosetGeometry.stabilizer_base]
    cases j
    · exact reduced_binary_neighbor_center_noncentral h 0 hn e hF
    · exact reduced_binary_neighbor_center_noncentral h 1 hn e hF
  exact reduced_linear_escaping_neighbor h j hn e hnc

variable {K : Type*} [Field K] [Finite K] [CharP K 2]
/-- The original binary branch supplies an odd mover of the closure core, with all order and inclusion maps retained. -/
theorem reduced_binary_core_pair (h : HypothesisF11 L S) (j : Bool)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data
      (other (if j then 1 else 0)))) ≤ normalizer
      (↑(((P₀ L S (if j then 1 else 0)).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other (if j then 1 else 0))).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)))
    (e : (L (other (if j then 1 else 0)) ⧸ pCore 2 (L (other (if j then 1 else 0)))) ≃* PSL(2,F))
    (eδ : (family L j ⧸ pCore 2 (family L j)) ≃* PSL(2,K))
    (hF : Nat.card F = 2) :
    let Δ := reducedFamily L S
    let δ := base Δ j
    let lam := base Δ (!j)
    let X := conjugateSpanBy (Q Δ δ) (stabilizer Δ lam)
    (¬ V Δ δ 1 ≤ X.pCoreIn 2) ∧
    ∃ (mu : Vertex Δ) (x : G₀ L S),
      (graph Δ).Adj δ mu ∧
      x ∈ graphLocalGroup Δ δ ∧ Odd (orderOf x) ∧ x • lam = mu ∧
      (x : G) ∈ family (enlargedEndpoint L S) j ∧ Odd (orderOf (x : G)) ∧
      Z Δ mu ≤ Q Δ δ ∧ ¬ Z Δ mu ≤ X.pCoreIn 2 ∧
      (Q Δ δ).map (MulAut.conj x).toMonoidHom = Q Δ δ ∧
      (X.pCoreIn 2).map (MulAut.conj x).toMonoidHom =
        (conjugateSpanBy (Q Δ δ) (stabilizer Δ mu)).pCoreIn 2 ∧
      (X.pCoreIn 2).map (MulAut.conj x).toMonoidHom ≠ X.pCoreIn 2 := by
  have hnc : ¬ Z (reducedFamily L S) (base (reducedFamily L S) (!j)) ≤ centralizer
      (conjugateSpanBy (Q (reducedFamily L S) (base (reducedFamily L S) j))
        (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!j))) : Set (G₀ L S)) := by
    simp only [Z,Q,stabilizer,Subgroup.CosetGeometry.stabilizer_base]
    cases j
    · exact reduced_binary_neighbor_center_noncentral h 0 hn e hF
    · exact reduced_binary_neighbor_center_noncentral h 1 hn e hF
  exact reduced_linear_noncentral_core_pair h j hn e eδ hnc

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
