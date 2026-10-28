module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.Reorientation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.FixedGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.Centralizers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.Actions
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.Reduced

/-!
# The neighborhood and reorientation arguments on the reduced F.1.11 graph

Apply the graph lemmas to the already constructed reduced triple, using
its actual stabilizers, two-cores, Sylow-center spans and two-orbit minimum.
The center/core inclusions are discharged by `source_Z_Q_U`. The earlier
DGS 6.2(d) Sylow assertion remains explicit in the original APIs. The
new centralizer and action applications discharge it from the reduced
source setup; `InitialGeometry` also supplies the required b > 2 from the
commuting critical assumptions. The exchange application retains its
literal element in the reduced completion.

The final application carries fixed-space generation through the supplied
homomorphism of the same vertex group, with the same Sylow and normal
local subgroup. These are local steps for 9.1--9.4, not the distance-three
or field-two conclusion of Chapter 9.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 9.1--9.4, printed pp.141--143; Aschbacher--Smith F.1.9.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The elementary and quadratic steps of 9.1(c), plus forward escape, on the reduced source graph. -/
theorem reduced_neighbor_quadratic (h : HypothesisF11 L S)
    (hSylow : ∀ v : Vertex (Reduction.reducedFamily L S),
      ∃ T : Sylow 2 (U (Reduction.reducedFamily L S) v),
        (T : Subgroup (U (Reduction.reducedFamily L S) v)).map
          (U (Reduction.reducedFamily L S) v).subtype = Q (Reduction.reducedFamily L S) v)
    {a a' beta : Vertex (Reduction.reducedFamily L S)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S) a a')
    (ha : (graph (Reduction.reducedFamily L S)).Adj beta a)
    (hb : 2 < b (Reduction.reducedFamily L S))
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S)) :
    let F := Reduction.reducedFamily L S
    V F beta 1 ≤ Q F beta ∧ V F a' 1 ≤ Q F a' ∧
    IsElementaryAbelian 2 (V F beta 1) ∧ IsElementaryAbelian 2 (V F a' 1) ∧
    ⁅⁅V F beta 1, V F a' 1⁆, V F beta 1⁆ = ⊥ ∧
    ⁅⁅V F beta 1, V F a' 1⁆, V F a' 1⁆ = ⊥ ∧ ¬ V F beta 1 ≤ Q F a' := by
  dsimp only
  have ht := Reduction.reduced_triple h
  let : ∀ i, Finite (Reduction.reducedFamily L S i) := finite_endpoints ht
  have hgen : Reduction.reducedFamily L S false ⊔ Reduction.reducedFamily L S true = ⊤ :=
    ht.generate
  have hZ : ∀ v : Vertex (Reduction.reducedFamily L S),
      Z (Reduction.reducedFamily L S) v ≤ omegaCenterIn (Q (Reduction.reducedFamily L S) v) :=
    fun v => (source_Z_Q_U ht v).1
  have hquad := V_mutual_quadratic (Reduction.reducedFamily L S) hgen hZ hSylow beta a' hb hd.le
  exact ⟨V_le_Q (Reduction.reducedFamily L S) hgen hZ hSylow beta (by omega),
    V_le_Q (Reduction.reducedFamily L S) hgen hZ hSylow a' (by omega),
    V_elementary (Reduction.reducedFamily L S) hgen hZ hSylow beta (by simpa using hb),
    V_elementary (Reduction.reducedFamily L S) hgen hZ hSylow a' (by simpa using hb),
    hquad.1, hquad.2, V_not_le_Q_of_criticalPair _ hc ha (source_Z_Q_U ht a').2⟩

/-- The neighboring critical-pair selection of 9.2 on the literal reduced graph. -/
theorem reduced_reverse_criticalPair (h : HypothesisF11 L S)
    (hSylow : ∀ v : Vertex (Reduction.reducedFamily L S),
      ∃ T : Sylow 2 (U (Reduction.reducedFamily L S) v),
        (T : Subgroup (U (Reduction.reducedFamily L S) v)).map
          (U (Reduction.reducedFamily L S) v).subtype = Q (Reduction.reducedFamily L S) v)
    {a' beta : Vertex (Reduction.reducedFamily L S)}
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S))
    (he : ¬ V (Reduction.reducedFamily L S) a' 1 ≤ Q (Reduction.reducedFamily L S) beta) :
    ∃ z : Vertex (Reduction.reducedFamily L S),
      (graph (Reduction.reducedFamily L S)).Adj a' z ∧
      IsCriticalPair (Reduction.reducedFamily L S) z beta ∧
      ¬ Z (Reduction.reducedFamily L S) z ≤ Q (Reduction.reducedFamily L S) beta := by
  have ht := Reduction.reduced_triple h
  let : ∀ i, Finite (Reduction.reducedFamily L S i) := finite_endpoints ht
  have hgen : Reduction.reducedFamily L S false ⊔ Reduction.reducedFamily L S true = ⊤ :=
    ht.generate
  exact exists_neighbor_criticalPair (Reduction.reducedFamily L S) hgen (fun v => (source_Z_Q_U ht v).1)
    hSylow (by rwa [SimpleGraph.dist_comm]) he

/-- The last conjugation step of 9.2 with an element of the actual reduced completion. -/
theorem reduced_reverse_commutator_of_exchange (h : HypothesisF11 L S)
    {a' beta : Vertex (Reduction.reducedFamily L S)}
    (hcomm : ⁅V (Reduction.reducedFamily L S) beta 1 ⊓ Q (Reduction.reducedFamily L S) a',
      V (Reduction.reducedFamily L S) a' 1⁆ = ⊥)
    (g : Reduction.G₀ L S) (hg : g • beta = a') (hg' : g • a' = beta) :
    ⁅V (Reduction.reducedFamily L S) a' 1 ⊓ Q (Reduction.reducedFamily L S) beta,
      V (Reduction.reducedFamily L S) beta 1⁆ = ⊥ := by
  let : ∀ i, Finite (Reduction.reducedFamily L S i) :=
    finite_endpoints (Reduction.reduced_triple h)
  exact reverse_commutator_eq_bot_of_exchange (Reduction.reducedFamily L S) hcomm g hg hg'

/-- Fixed-space generation for the original reduced-graph Z and the supplied literal image. -/
theorem reduced_Z_image_fixedSpace_generation {D : Type*} [Group D]
    (h : HypothesisF11 L S) (v : Vertex (Reduction.reducedFamily L S))
    (T : Sylow 2 (stabilizer (Reduction.reducedFamily L S) v))
    (H : Subgroup (stabilizer (Reduction.reducedFamily L S) v)) [H.Normal]
    (hTH : (T : Subgroup (stabilizer (Reduction.reducedFamily L S) v)) ≤ H)
    (f : stabilizer (Reduction.reducedFamily L S) v →* D) :
    let F := Reduction.reducedFamily L S
    ((Z F v).subgroupOf (stabilizer F v)).map f =
      conjugateSpanBy (((Z F v).subgroupOf (stabilizer F v)).map f ⊓
        centralizer ((T : Subgroup (stabilizer F v)).map f : Set D)) (H.map f) := by
  let : ∀ i, Finite (Reduction.reducedFamily L S i) :=
    finite_endpoints (Reduction.reduced_triple h)
  exact Z_image_fixedSpace_generation (Reduction.reducedFamily L S) v T H hTH f

/-- Source 9.1(d) on the literal reduced F.1.11 graph; no additional local
centralizer or faithfulness premise is required. -/
theorem reduced_neighborhood_centralizer (h : HypothesisF11 L S)
    (v : Vertex (Reduction.reducedFamily L S)) :
    stabilizer (Reduction.reducedFamily L S) v ⊓
      centralizer (V (Reduction.reducedFamily L S) v 1 : Set (Reduction.G₀ L S)) ≤
        U (Reduction.reducedFamily L S) v :=
  neighborhood_centralizer_le_U (Reduction.reduced_triple h) v

/-- The 9.3 forward centralizer identity with the actual reduced actor,
space, and core. Earlier 6.2(d) is discharged by the genuine reduced setup. -/
theorem reduced_neighbor_centralizer_eq_core_inter (h : HypothesisF11 L S)
    (beta a' : Vertex (Reduction.reducedFamily L S))
    (hb : 1 < b (Reduction.reducedFamily L S))
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S))
    (hc : ⁅V (Reduction.reducedFamily L S) beta 1 ⊓ Q (Reduction.reducedFamily L S) a',
      V (Reduction.reducedFamily L S) a' 1⁆ = ⊥) :
    V (Reduction.reducedFamily L S) beta 1 ⊓
      centralizer (V (Reduction.reducedFamily L S) a' 1 : Set (Reduction.G₀ L S)) =
        V (Reduction.reducedFamily L S) beta 1 ⊓ Q (Reduction.reducedFamily L S) a' :=
  neighbor_span_centralizer_eq_core_inter (Reduction.reduced_triple h)
    (Reduction.reduced_kernel_sylow h) beta a' hb hd.le hc

/-- The source actor for the quotient V_beta/(V_beta intersect Q_alpha')
on V_alpha'. -/
noncomputable def reduced_neighbor_action (h : HypothesisF11 L S)
    (beta a' : Vertex (Reduction.reducedFamily L S))
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 ≤
      b (Reduction.reducedFamily L S)) :
    V (Reduction.reducedFamily L S) beta 1 →*
      MulAut (V (Reduction.reducedFamily L S) a' 1) := by
  let : ∀ i, Finite (Reduction.reducedFamily L S i) :=
    finite_endpoints (Reduction.reduced_triple h)
  exact neighborAction (Reduction.reducedFamily L S) (Reduction.reduced_triple h).generate
    beta a' hd

/-- The kernel and actual quotient actor on the same reduced source groups. -/
theorem reduced_neighbor_action_kernel (h : HypothesisF11 L S)
    (beta a' : Vertex (Reduction.reducedFamily L S))
    (hb : 1 < b (Reduction.reducedFamily L S))
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 ≤
      b (Reduction.reducedFamily L S))
    (hc : ⁅V (Reduction.reducedFamily L S) beta 1 ⊓ Q (Reduction.reducedFamily L S) a',
      V (Reduction.reducedFamily L S) a' 1⁆ = ⊥) :
    (reduced_neighbor_action h beta a' hd).ker =
      (Q (Reduction.reducedFamily L S) a').subgroupOf
        (V (Reduction.reducedFamily L S) beta 1) := by
  have hk := neighborAction_ker (Reduction.reduced_triple h)
    (fun v => Reduction.reduced_kernel_sylow h v) beta a' hb hd hc
  exact hk

/-- The literal original source quotient is equivalent to its conjugation image. -/
theorem reduced_neighbor_action_quotient (h : HypothesisF11 L S)
    (beta a' : Vertex (Reduction.reducedFamily L S))
    (hb : 1 < b (Reduction.reducedFamily L S))
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 ≤
      b (Reduction.reducedFamily L S))
    (hc : ⁅V (Reduction.reducedFamily L S) beta 1 ⊓ Q (Reduction.reducedFamily L S) a',
      V (Reduction.reducedFamily L S) a' 1⁆ = ⊥) :
    letI := neighborCoreInter_normal (Reduction.reducedFamily L S)
      (Reduction.reduced_triple h).generate beta a' hd
    ∃ e : (V (Reduction.reducedFamily L S) beta 1 ⧸
        (Q (Reduction.reducedFamily L S) a').subgroupOf
          (V (Reduction.reducedFamily L S) beta 1)) ≃*
        (reduced_neighbor_action h beta a' hd).range,
      ∀ x : V (Reduction.reducedFamily L S) beta 1,
        (e (QuotientGroup.mk' _ x) : MulAut (V (Reduction.reducedFamily L S) a' 1)) =
          reduced_neighbor_action h beta a' hd x := by
  have he := neighborAction_quotient_equiv (Reduction.reduced_triple h)
    (fun v => Reduction.reduced_kernel_sylow h v) beta a' hb hd hc
  exact he

/-- Escape of the same critical pair gives a genuinely nontrivial quotient actor. -/
theorem reduced_neighbor_action_nontrivial (h : HypothesisF11 L S)
    (beta a' : Vertex (Reduction.reducedFamily L S))
    (hb : 1 < b (Reduction.reducedFamily L S))
    (hd : (graph (Reduction.reducedFamily L S)).dist beta a' + 1 ≤
      b (Reduction.reducedFamily L S))
    (hc : ⁅V (Reduction.reducedFamily L S) beta 1 ⊓ Q (Reduction.reducedFamily L S) a',
      V (Reduction.reducedFamily L S) a' 1⁆ = ⊥)
    (he : ¬ V (Reduction.reducedFamily L S) beta 1 ≤ Q (Reduction.reducedFamily L S) a') :
    1 < Nat.card (reduced_neighbor_action h beta a' hd).range := by
  have hn := neighborAction_range_one_lt (Reduction.reduced_triple h)
    (fun v => Reduction.reduced_kernel_sylow h v) beta a' hb hd hc he
  exact hn

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
