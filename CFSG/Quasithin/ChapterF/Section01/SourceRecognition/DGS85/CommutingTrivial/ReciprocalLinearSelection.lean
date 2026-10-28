module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.SmallUnitaryConstituents
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ConstituentExclusions
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ConstituentIndices

/-!
# Recognizing the reciprocal local quotients and their original indices

The large-parameter exclusions leave only linear groups and the two unitary
models over the field of order two. The new constituent bounds exclude both
small unitary models: the original centralizer identities and conjugation
transport give x² ≤ y and y² ≤ x, while critical escape gives x > 1.
Thus the full supplied rank-one catalogue yields an actual SL₂ marking.
Applying the existing linear field bounds identifies both original core
indices and the opposite centralizer index with its defining-field order.

The Chapter 8 exchange conclusion and the earlier actual quotient catalogue
remain explicit source inputs. No SL₂ marking, whole residual descent or
naturality is assumed. The small-neighbor recognition, natural sections,
distance bound and final field-two conclusion remain with Chapter 9 assembly.
Source: DGS, *Groups and Graphs* (1985), (9.2)--(9.3), printed p.142.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The reciprocal branch selects an actual linear quotient from the full
rank-one catalogue, including exclusion of both field-two unitary models. -/
theorem reduced_large_neighbor_linear_marking (h : HypothesisF11 L S₀)
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
    (M : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta))) :
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧
      Nonempty ((graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F)) := by
  rcases reduced_large_neighbor_rank_one_alternatives h hc hab hd hb hcomm htriv he h8 M
    with hlin | hsmall
  · exact hlin
  exfalso
  obtain ⟨F,instF,instFin,J,hcard,hconj,hmodel⟩ := hsmall
  let := instF
  let := instFin
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hrev := reduced_reverse_displacement_of_chapterEight h hc hab hd hb hcomm htriv he h8
  obtain ⟨z,hz,hzc,_⟩ := reduced_reverse_criticalPair h (Reduction.reduced_kernel_sylow h) hd he
  have hzcomm : ⁅Z Γ z,Z Γ beta⁆ = ⊥ := reverse_critical_centers_commute ht hzc
    (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
  have hd' : (graph Γ).dist a' beta + 1 = b Γ := by rwa [SimpleGraph.dist_comm]
  obtain ⟨g,e₀,f,hg,he₀,hf,_⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  have hbounds :
      ((Q Γ beta).relIndex (V Γ a' 1)) ^ 2 ≤
        (centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) ∧
      ((Q Γ a').relIndex (V Γ beta 1)) ^ 2 ≤
        (centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) := by
    rcases hmodel with hsu | hpsu
    · obtain ⟨e⟩ := hsu
      exact ⟨reduced_critical_small_special_unitary_constituent_bound h hc hab hd hb hcomm
        J hcard hconj e,
        reduced_critical_small_special_unitary_constituent_bound h hzc hz.symm hd' hb hzcomm
        J hcard hconj (f.trans e)⟩
    · obtain ⟨e⟩ := hpsu
      exact ⟨reduced_critical_small_projective_unitary_constituent_bound h hc hab hd hb hcomm
        J hcard hconj e,
        reduced_critical_small_projective_unitary_constituent_bound h hzc hz.symm hd' hb hzcomm
        J hcard hconj (f.trans e)⟩
  obtain ⟨hlo,hlo'⟩ := hbounds
  have hc₁ := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ beta 1))
    (reduced_neighbor_centralizer_eq_core_inter h beta a' hb hd htriv)
  have hc₂ := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ a' 1))
    (reduced_neighbor_centralizer_eq_core_inter h a' beta hb hd' hrev)
  change (V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) =
    (V Γ beta 1 ⊓ Q Γ a').relIndex (V Γ beta 1) at hc₁
  change (V Γ a' 1 ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) =
    (V Γ a' 1 ⊓ Q Γ beta).relIndex (V Γ a' 1) at hc₂
  simp only [inf_relIndex_left] at hc₁ hc₂
  rw [hc₁] at hlo
  rw [hc₂] at hlo'
  have hv := V_le_stabilizer Γ ht.generate beta beta
    (show (graph Γ).dist beta beta + 1 ≤ b Γ by simpa only [SimpleGraph.dist_self,zero_add] using hb.le)
  let : Finite (V Γ beta 1) := Finite.of_injective (inclusion hv) (inclusion_injective _)
  have heforward : ¬ V Γ beta 1 ≤ Q Γ a' :=
    V_not_le_Q_of_criticalPair Γ hc hab.symm (source_Z_Q_U ht a').2
  have hx : 1 < (Q Γ a').relIndex (V Γ beta 1) :=
    one_lt_index_of_ne_top (fun heq => heforward (subgroupOf_eq_top.mp heq))
  have hy : (Q Γ beta).relIndex (V Γ a' 1) ≤ ((Q Γ beta).relIndex (V Γ a' 1)) ^ 2 :=
    Nat.le_self_pow (by decide) _
  have hbad := hlo'.trans (hy.trans hlo)
  nlinarith

/-- Source (9.3)(a)--(b) in the reciprocal branch: both actual local quotients
are recognized over one field, and the literal original indices equal its order. -/
theorem reduced_large_neighbor_recognized_indices (h : HypothesisF11 L S₀)
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
    (M : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta))) :
    let Γ := Reduction.reducedFamily L S₀
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧
      Nonempty ((graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F)) ∧
      Nonempty ((graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')) ≃* SL(2,F)) ∧
      (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧
      (Q Γ beta).relIndex (V Γ a' 1) = Nat.card F ∧
      (centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) = Nat.card F := by
  obtain ⟨F,instF,instFin,instChar,n,hn,hF,⟨e⟩⟩ :=
    reduced_large_neighbor_linear_marking h hc hab hd hb hcomm htriv he h8 M
  let := instF
  let := instFin
  let := instChar
  obtain ⟨g,e₀,f,hg,he₀,hf,_⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  exact ⟨F,instF,instFin,instChar,n,hn,hF,⟨e⟩,⟨f.trans e⟩,
    reduced_large_neighbor_linear_indices h hc hab hd hb hcomm htriv he h8 hn hF e⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
