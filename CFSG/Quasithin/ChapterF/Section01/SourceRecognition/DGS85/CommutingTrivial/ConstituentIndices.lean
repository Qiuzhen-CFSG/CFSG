module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ConstituentBounds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReverseDisplacement

/-!
# The original indices in the reciprocal linear branch

The neighboring local quotients are identified by the original graph action.
At each one, the constructed constituent bounds the opposing core index
above and the centralizer index below by the same field order. The source
centralizer identities make both original indices equal to that order.

This proves 9.3(b) on the reciprocal linear branch without a whole-section
quotient action. The explicit linear marking remains to be established by
initial recognition; h8 is produced by qt-dgs85-critical-commuting-nontrivial
and discharged by final source assembly. Naturality of the whole residual
section and the terminal Chapter 9 conclusions remain separate obligations.
Source: DGS, *Groups and Graphs* (1985), 9.3(b), printed p.142.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The exact two equalities of 9.3(b) in the reciprocal linear branch,
without assuming descent or naturality of the whole residual section. -/
theorem reduced_large_neighbor_linear_indices (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓ Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (he : ¬ V (Reduction.reducedFamily L S₀) a' 1 ≤ Q (Reduction.reducedFamily L S₀) beta)
    (h8 : ∀ z : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj z a' →
      IsCriticalPair (Reduction.reducedFamily L S₀) z beta →
      ⁅Z (Reduction.reducedFamily L S₀) z, Z (Reduction.reducedFamily L S₀) beta⁆ = ⊥ →
      ⁅V (Reduction.reducedFamily L S₀) a' 1 ⊓ Q (Reduction.reducedFamily L S₀) beta,
        V (Reduction.reducedFamily L S₀) beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b (Reduction.reducedFamily L S₀) = 3 ∧
          Nonempty ((graphLocalGroup (Reduction.reducedFamily L S₀) z ⧸
            pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) z)) ≃* SL(2,F)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F)) :
    let Γ := Reduction.reducedFamily L S₀
    (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧
      (Q Γ beta).relIndex (V Γ a' 1) = Nat.card F ∧
      (centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) = Nat.card F := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hrev := reduced_reverse_displacement_of_chapterEight h hc hab hd hb hcomm htriv he h8
  obtain ⟨z,hz,hzc,_⟩ := reduced_reverse_criticalPair h (Reduction.reduced_kernel_sylow h) hd he
  have hzcomm : ⁅Z Γ z,Z Γ beta⁆ = ⊥ := reverse_critical_centers_commute ht hzc
    (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
  have hd' : (graph Γ).dist a' beta + 1 = b Γ := by rwa [SimpleGraph.dist_comm]
  obtain ⟨g,e₀,f,hg,he₀,hf,_⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  have heforward : ¬ V Γ beta 1 ≤ Q Γ a' :=
    V_not_le_Q_of_criticalPair Γ hc hab.symm (source_Z_Q_U ht a').2
  obtain ⟨hy,hlx⟩ := reduced_critical_linear_constituent_field_bounds h hc hab hd hb hcomm he hn hF e
  obtain ⟨hx,hly⟩ := reduced_critical_linear_constituent_field_bounds h hzc hz.symm hd' hb hzcomm
    heforward hn hF (f.trans e)
  have hc₁ := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ beta 1))
    (reduced_neighbor_centralizer_eq_core_inter h beta a' hb hd htriv)
  have hc₂ := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ a' 1))
    (reduced_neighbor_centralizer_eq_core_inter h a' beta hb hd' hrev)
  change (V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) =
    (V Γ beta 1 ⊓ Q Γ a').relIndex (V Γ beta 1) at hc₁
  change (V Γ a' 1 ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) =
    (V Γ a' 1 ⊓ Q Γ beta).relIndex (V Γ a' 1) at hc₂
  simp only [inf_relIndex_left] at hc₁ hc₂
  rw [hc₁] at hlx
  rw [hc₂] at hly
  exact ⟨le_antisymm hx hlx,le_antisymm hy hly,hc₂.trans (le_antisymm hy hly)⟩


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
