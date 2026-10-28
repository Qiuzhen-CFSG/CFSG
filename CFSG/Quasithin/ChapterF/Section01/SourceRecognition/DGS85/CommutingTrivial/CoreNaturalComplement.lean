module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.AdaptedCoreElementary
public import Theory.Representation.SL2.NaturalSelfExtension
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction

/-!
# An elementary natural complement in the original core

Once 9.10(4)–(5) identify the adjacent-core intersection with V, the two
natural factors of the literal Q/Z module split relative to the image of V.
Pulling the complement back constructs the original adapted subgroup W.
Centrality of Z in the actor proves that W is elementary; the graph core
obstruction forces W to escape the neighboring core.

Source: DGS, *Groups and Graphs* (1985), 9.10(6), printed pp.149–150.
The intersection equality remains the output of the earlier Cartan argument.
-/

public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual adapted elementary subgroup, constructed from the source layers. -/
theorem reduced_core_natural_complement
    (h : HypothesisF11 L S)
    {a beta x : Vertex (Reduction.reducedFamily L S)}
    (hbx : (graph (Reduction.reducedFamily L S)).Adj beta x)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eβ : (graphLocalGroup (Reduction.reducedFamily L S) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) beta)) ≃* SL(2,F))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2^n)
    (hres : NaturalResidualSection h beta eβ n)
    (hsec : CoreQuotientSection (Reduction.reducedFamily L S) a beta x F eβ)
    (hNspan : Q (Reduction.reducedFamily L S) a ⊓ Q (Reduction.reducedFamily L S) x =
      V (Reduction.reducedFamily L S) beta 1)
    (hω : Z (Reduction.reducedFamily L S) beta =
      omegaCenterIn (graphLocalGroup (Reduction.reducedFamily L S) beta))
    (hc : ⁅Q (Reduction.reducedFamily L S) beta,V (Reduction.reducedFamily L S) beta 1⁆ ≤
      Z (Reduction.reducedFamily L S) beta)
    (hVcard : Nat.card (V (Reduction.reducedFamily L S) beta 1) = Nat.card F ^ 3)
    (hZcard : Nat.card (Z (Reduction.reducedFamily L S) beta) = Nat.card F) :
    let Γ := Reduction.reducedFamily L S
    let π := eβ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta)))
    letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    ⁅Q Γ beta,Q Γ beta⁆ ≤ Z Γ beta ∧
      ∃ W : Subgroup (Reduction.G₀ L S), W ≤ Q Γ beta ∧
        W ⊓ V Γ beta 1 = Z Γ beta ∧ W ⊔ V Γ beta 1 = Q Γ beta ∧
        Nat.card W = Nat.card F ^ 3 ∧ ¬ W ≤ Q Γ x ∧ IsElementaryAbelian 2 W ∧
        Nonempty (BinaryConjugationSection (graphLocalGroup Γ beta) W (Z Γ beta)
          (((specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)).comp π)) := by
  let Γ := Reduction.reducedFamily L S
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨hZ,hQQ,hE,ρ,c,_,X,eX,eQ,heX,heQ,hX⟩ :=
    reduced_core_factors_of_intersection_eq_span h eβ hn hF hres hsec hNspan hω hc
      hVcard hZcard
  let := hZ
  let := hE
  obtain ⟨K,hK,eK,heK⟩ := SL2NaturalSelfExtension.exists_natural_complement ρ X eX eQ heX heQ
  have hVQ : V Γ beta 1 ≤ Q Γ beta := by
    obtain ⟨_,_,_,_,d,_⟩ := hsec
    exact hNspan ▸ d.kernel_le
  have hVx : V Γ beta 1 ≤ Q Γ x := hNspan ▸ inf_le_right
  have hQx : ¬ Q Γ beta ≤ Q Γ x := core_escape_of_intersection_obstruction Γ
    (Reduction.reduced_graph_core_obstruction h beta x hbx)
  have hbig : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  obtain ⟨W,hWQ,hWV,hWsup,hWcard,hWesc,hWE,cW,_⟩ :=
    adapted_core_complement_elementary Γ beta x eβ ρ c hVQ X K hX hK eK heK
      hZcard hVx hQx hω hbig
  exact ⟨hQQ,W,hWQ,hWV,hWsup,hWcard,hWesc,hWE,⟨cW⟩⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
