module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ConstituentBounds
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.ReverseDisplacement

/-!
# Initial quotient selection in the reciprocal commuting branch

Transport the original local quotient from beta to alpha-prime and apply
the constituent square bound in both orientations. The source centralizer
identities would give x² ≤ y and y² ≤ x with x > 1. This excludes every
Suzuki model and both unitary models of degree at least two, before any
whole-section descent. Actual linear quotients and the two small unitary
models remain in the supplied Chapter 5 catalogue.

The explicit h8 premise is the earlier 8.4/8.6 conclusion produced by
qt-dgs85-critical-commuting-nontrivial. Final source assembly retains its
discharge. This module does not handle the small-neighbor branch, eliminate
the small unitary models, or prove the terminal distance and field bounds.
Source: DGS, *Groups and Graphs* (1985), 9.2--9.3, printed p.142.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}

/-- The original reciprocal commuting configuration excludes every actual
Suzuki quotient, including Sz(2), using the earlier Chapter 8 exchange. -/
theorem reduced_large_neighbor_not_suzuki (h : HypothesisF11 L S₀)
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
    (m : ℕ)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hrev := reduced_reverse_displacement_of_chapterEight h hc hab hd hb hcomm htriv he h8
  obtain ⟨z,hz,hzc,_⟩ := reduced_reverse_criticalPair h (Reduction.reduced_kernel_sylow h) hd he
  have hzcomm : ⁅Z Γ z,Z Γ beta⁆ = ⊥ := reverse_critical_centers_commute ht hzc
    (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
  have hd' : (graph Γ).dist a' beta + 1 = b Γ := by rwa [SimpleGraph.dist_comm]
  obtain ⟨g,e₀,f,hg,he₀,hf,_⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  have hlo := reduced_critical_suzuki_constituent_bound h hc hab hd hb hcomm m e
  have hlo' := reduced_critical_suzuki_constituent_bound h hzc hz.symm hd' hb hzcomm m (f.trans e)
  have hc₁ := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ beta 1))
    (reduced_neighbor_centralizer_eq_core_inter h beta a' hb hd htriv)
  have hc₂ := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ a' 1))
    (reduced_neighbor_centralizer_eq_core_inter h a' beta hb hd' hrev)
  change (V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) =
    (V Γ beta 1 ⊓ Q Γ a').relIndex (V Γ beta 1) at hc₁
  change (V Γ a' 1 ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) =
    (V Γ a' 1 ⊓ Q Γ beta).relIndex (V Γ a' 1) at hc₂
  simp only [inf_relIndex_left] at hc₁ hc₂
  change ((Q Γ beta).relIndex (V Γ a' 1)) ^ 2 ≤ _ at hlo
  change ((Q Γ a').relIndex (V Γ beta 1)) ^ 2 ≤ _ at hlo'
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

/-- The reciprocal commuting branch excludes this actual unitary quotient
at every field parameter of degree at least two. The quotient at the other
vertex is transported by the original graph action. -/
theorem reduced_large_neighbor_not_special_unitary (h : HypothesisF11 L S₀)
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
    {K : Type*} [Field K] [Finite K] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 K)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃*
        J.specialSubgroup) : False := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hrev := reduced_reverse_displacement_of_chapterEight h hc hab hd hb hcomm htriv he h8
  obtain ⟨z,hz,hzc,_⟩ := reduced_reverse_criticalPair h (Reduction.reduced_kernel_sylow h) hd he
  have hzcomm : ⁅Z Γ z,Z Γ beta⁆ = ⊥ := reverse_critical_centers_commute ht hzc
    (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
  have hd' : (graph Γ).dist a' beta + 1 = b Γ := by rwa [SimpleGraph.dist_comm]
  obtain ⟨g,e₀,f,hg,he₀,hf,_⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  have hlo := reduced_critical_special_unitary_constituent_bound h hc hab hd hb hcomm J hn hK hconj e
  have hlo' := reduced_critical_special_unitary_constituent_bound h hzc hz.symm hd' hb hzcomm J hn hK hconj (f.trans e)
  have hc₁ := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ beta 1))
    (reduced_neighbor_centralizer_eq_core_inter h beta a' hb hd htriv)
  have hc₂ := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ a' 1))
    (reduced_neighbor_centralizer_eq_core_inter h a' beta hb hd' hrev)
  change (V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) =
    (V Γ beta 1 ⊓ Q Γ a').relIndex (V Γ beta 1) at hc₁
  change (V Γ a' 1 ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) =
    (V Γ a' 1 ⊓ Q Γ beta).relIndex (V Γ a' 1) at hc₂
  simp only [inf_relIndex_left] at hc₁ hc₂
  change ((Q Γ beta).relIndex (V Γ a' 1)) ^ 2 ≤ _ at hlo
  change ((Q Γ a').relIndex (V Γ beta 1)) ^ 2 ≤ _ at hlo'
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

/-- The reciprocal commuting branch excludes this actual unitary quotient
at every field parameter of degree at least two. The quotient at the other
vertex is transported by the original graph action. -/
theorem reduced_large_neighbor_not_projective_unitary (h : HypothesisF11 L S₀)
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
    {K : Type*} [Field K] [Finite K] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 K)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃*
        BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) : False := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hrev := reduced_reverse_displacement_of_chapterEight h hc hab hd hb hcomm htriv he h8
  obtain ⟨z,hz,hzc,_⟩ := reduced_reverse_criticalPair h (Reduction.reduced_kernel_sylow h) hd he
  have hzcomm : ⁅Z Γ z,Z Γ beta⁆ = ⊥ := reverse_critical_centers_commute ht hzc
    (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
  have hd' : (graph Γ).dist a' beta + 1 = b Γ := by rwa [SimpleGraph.dist_comm]
  obtain ⟨g,e₀,f,hg,he₀,hf,_⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
  have hlo := reduced_critical_projective_unitary_constituent_bound h hc hab hd hb hcomm J hn hK hconj e
  have hlo' := reduced_critical_projective_unitary_constituent_bound h hzc hz.symm hd' hb hzcomm J hn hK hconj (f.trans e)
  have hc₁ := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ beta 1))
    (reduced_neighbor_centralizer_eq_core_inter h beta a' hb hd htriv)
  have hc₂ := congrArg (fun C : Subgroup (Reduction.G₀ L S₀) => C.relIndex (V Γ a' 1))
    (reduced_neighbor_centralizer_eq_core_inter h a' beta hb hd' hrev)
  change (V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) =
    (V Γ beta 1 ⊓ Q Γ a').relIndex (V Γ beta 1) at hc₁
  change (V Γ a' 1 ⊓ centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) =
    (V Γ a' 1 ⊓ Q Γ beta).relIndex (V Γ a' 1) at hc₂
  simp only [inf_relIndex_left] at hc₁ hc₂
  change ((Q Γ beta).relIndex (V Γ a' 1)) ^ 2 ≤ _ at hlo
  change ((Q Γ a').relIndex (V Γ beta 1)) ^ 2 ≤ _ at hlo'
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

/-- Initial model selection in the reciprocal branch: only actual SL₂
quotients and the small SU₃(2)/PSU₃(2) quotients remain. The source catalogue
is the earlier input; no residual action descent or naturality is assumed. -/
theorem reduced_large_neighbor_rank_one_alternatives (h : HypothesisF11 L S₀)
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
    let D := graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)
    (∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧ Nonempty (D ≃* SL(2,F))) ∨
    (∃ (F : Type u) (_ : Field F) (_ : Finite F) (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F),
      Nat.card F = 4 ∧ (∀ x, J.conj x = x^2) ∧
      (Nonempty (D ≃* J.specialSubgroup) ∨
        Nonempty (D ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J))) := by
  cases M with
  | sl2 F n hn hF e => exact Or.inl ⟨F,inferInstance,inferInstance,inferInstance,n,hn,hF,⟨e⟩⟩
  | suzuki m e =>
      exact (reduced_large_neighbor_not_suzuki h hc hab hd hb hcomm htriv he h8 m e).elim
  | su3 F J n hn hF hconj e =>
      have hn1 : n = 1 := by
        by_contra hn1
        exact reduced_large_neighbor_not_special_unitary h hc hab hd hb hcomm htriv he h8
          J (by omega) hF hconj e
      exact Or.inr ⟨F,inferInstance,inferInstance,J,
        by simpa [hn1] using hF,
        by simpa only [hn1,pow_one] using hconj,Or.inl ⟨e⟩⟩
  | psu3 F J n hn hF hconj e =>
      have hn1 : n = 1 := by
        by_contra hn1
        exact reduced_large_neighbor_not_projective_unitary h hc hab hd hb hcomm htriv he h8
          J (by omega) hF hconj e
      exact Or.inr ⟨F,inferInstance,inferInstance,J,
        by simpa [hn1] using hF,
        by simpa only [hn1,pow_one] using hconj,Or.inr ⟨e⟩⟩


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
