module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiExactCoreOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SourceRootTransitivityLowerBound
public import Theory.GroupTheory.AmalgamGraph.OddPathTransitivity
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSourceUpperBound
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SourceParameter

/-!
# Exact source path length in the nonbinary commuting branch

The linear core has order q¹¹ and its index in the common Sylow is q.
The existing q¹² upper bound therefore identifies the order of the
full Borel two-core, including the original completion. All edge
cores have this same order by conjugacy.

There are exactly q¹² nine-paths through either orientation of an
edge. Their odd fixers make the edge two-core action free. Counting
forces rooted transitivity through length nine, so s = 9. Every
shorter nonbacktracking path is regular, whereas no longer one is:
its odd fixer cannot be transitive on an even set of forward neighbors.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.9)(c), printed pp.186--190. Earlier markings, natural centers,
reciprocal commutators and the nonbinary parameter remain explicit.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial BenderSuzuki.MatrixGroups
open Theory.GroupAction.CubicTree Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The full original Borel two-core and every geometric edge two-core have order q¹². -/
theorem source_suzuki_exact_borel_order
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    Nat.card ((commonBorel L S).pCoreIn 2) = Nat.card k ^ 12 ∧
    ∀ {v w : Vertex (reducedFamily L S)}, (graph (reducedFamily L S)).Adj v w →
      Nat.card ((stabilizer (reducedFamily L S) v ⊓
        stabilizer (reducedFamily L S) w).pCoreIn 2) = Nat.card k ^ 12 := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let E := stabilizer F m ⊓ stabilizer F y
  let J := Q F y ⊔ Q F m
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hQym : Q F y ≤ stabilizer F m :=
    ((source_Z_Q_U (reduced_triple h) y).2.trans (ballKernel_one_le_edge F hadj.symm)).trans inf_le_right
  have hQmy : Q F m ≤ stabilizer F y :=
    ((source_Z_Q_U (reduced_triple h) m).2.trans (ballKernel_one_le_edge F hadj)).trans inf_le_right
  have hJE : J ≤ E := sup_le (le_inf hQym (Q_le_stabilizer F y))
    (le_inf (Q_le_stabilizer F m) hQmy)
  have hpJ : IsPGroup 2 J := by
    change IsPGroup 2 (Q F y ⊔ Q F m : Subgroup (G₀ L S))
    rw [←hT]
    exact T.isPGroup'.map (star L S i).subtype
  let : Finite E := Finite.of_injective (inclusion (show E ≤ stabilizer F m from inf_le_left)) (inclusion_injective _)
  have hJcore : J ≤ E.pCoreIn 2 := pGroup_le_core_of_core_sylow E J hJE hpJ
    (source_edge_core_sylow (reduced_triple h) (reduced_borel_core_sylow h) hadj)
  let : Finite (Q F m) := Finite.of_injective (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  let : Finite J := Finite.of_injective (inclusion hJE) (inclusion_injective _)
  let : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E)) (inclusion_injective _)
  obtain ⟨U,_,hiLin,_⟩ := source_common_sylow_core_index h i e T hT
  have hiL : (Q F y ⊓ Q F m).relIndex (Q F y) = Nat.card k :=
    hiLin.trans (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 U).symm.toEquiv)
  have hmJ : (Q F m).relIndex J = Nat.card k := by
    rw [show J = Q F y ⊔ Q F m from rfl,relIndex_sup_of_normalizes _ _
      (hQmy.trans (CommutingTrivial.stabilizer_normalizes_Q F y))]
    rwa [inf_relIndex_left] at hiL
  have hQcard := (source_suzuki_exact_core_orders h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).2.2.1
  have hJcard : Nat.card J = Nat.card k ^ 12 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) (Q F m) J bot_le le_sup_right
    rw [relIndex_bot_left,relIndex_bot_left,hmJ,hQcard] at hh
    exact hh.symm.trans (by ring)
  have hEbase : E = (B₀ L S).subgroupOf (G₀ L S) := by
    change stabilizer F (base F i) ⊓ stabilizer F (base F (!i)) = _
    simp only [stabilizer,Subgroup.CosetGeometry.stabilizer_base]
    cases i
    · exact (reduced_triple h).intersection
    · exact (inf_comm _ _).trans (reduced_triple h).intersection
  have hBG : B₀ L S ≤ G₀ L S :=
    (show B₀ L S ≤ P₀ L S 0 from le_sup_right).trans le_sup_left
  have hcore : (E.pCoreIn 2).map (G₀ L S).subtype = (commonBorel L S).pCoreIn 2 := by
    rw [hEbase,←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (G₀ L S).subtype_injective,
      map_subgroupOf_eq_of_le hBG,B₀_core h]
  have hB : Nat.card ((commonBorel L S).pCoreIn 2) = Nat.card k ^ 12 := by
    apply le_antisymm
    · simpa only [hfield] using source_suzuki_full_borel_core_upper h i hb3 T hT e hz hcard hcardy
        hzy hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hmin hnat hxadj hne hbranch
    · rw [←hcore,card_map_of_injective (G₀ L S).subtype_injective,←hJcard]
      exact Nat.card_le_card_of_injective (inclusion hJcore) (inclusion_injective _)
  have hbase : Nat.card ((F false ⊓ F true).pCoreIn 2) = Nat.card k ^ 12 := by
    have hint : F false ⊓ F true = (B₀ L S).subgroupOf (G₀ L S) := (reduced_triple h).intersection
    rw [hint,←hEbase]
    rw [←hcore,card_map_of_injective (G₀ L S).subtype_injective] at hB
    exact hB
  refine ⟨hB,?_⟩
  intro v w hvw
  obtain ⟨g,hg⟩ := edgeStabilizer_map_base F hvw
  rw [hg,Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (MulAut.conj g).injective,
    card_map_of_injective (MulAut.conj g).injective]
  exact hbase

/-- The literal minimum is nine; all and only the nonbacktracking paths of length at most eight are regular. -/
theorem source_suzuki_exact_path_parameter
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    let F := reducedFamily L S
    sourceS (P := fun j => (P₀ L S j).subgroupOf (G₀ L S)) = 9 ∧
    (∀ v : Vertex F, RootPathTransitive (graph F) (G₀ L S) v 9) ∧
    (∀ {r : ℕ} {v : Vertex F} (p : BasedWalk (graph F) r v), p.Nonbacktracking →
      (Regular (A := G₀ L S) p ↔ r ≤ 8)) ∧
    (∀ {r : ℕ} {v : Vertex F} (p : BasedWalk (graph F) r v), p.Nonbacktracking → 9 ≤ r →
      Odd (Nat.card (pathStabilizer F p)) ∧
      Odd (Nat.card ((pathStabilizer F p).map (G₀ L S).subtype))) := by
  let F := reducedFamily L S
  let q := 2^(2*n+1)
  let degree : Bool → ℕ := fun j => if j = i then q+1 else q^2+1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hval := source_linear_suzuki_neighbor_cards h i e eSuz hfield
  have hdeg : HasTwoNeighbors (graph F) := by
    intro v w
    apply Set.exists_ne_of_one_lt_ncard (s := (graph F).neighborSet v) _ w
    rw [←Nat.card_coe_set_eq,hval]
    have hq : 1 < 2^(2*n+1) := Nat.one_lt_pow (by omega) (by decide)
    split_ifs <;> nlinarith
  have hB {v w : Vertex F} (hvw : (graph F).Adj v w) :
      Nat.card ((stabilizer F v ⊓ stabilizer F w).pCoreIn 2) = Nat.card k ^ 12 :=
    (source_suzuki_exact_borel_order h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear).2 hvw
  have hodd {r : ℕ} {v : Vertex F} (p : BasedWalk (graph F) r v)
      (hp : p.Nonbacktracking) (hr : 9 ≤ r) := source_suzuki_long_path_odd h i hb3 T hT e hz hcard hcardy hzy hcommy
    hcross hsmall hactor hn eSuz hfield Ry hRy hmin hnat hxadj hne hbranch p hp hr
  have htrans (v : Vertex F) : RootPathTransitive (graph F) (G₀ L S) v 9 := by
    obtain ⟨p,hp,_⟩ := BasedWalk.exists_extension hdeg (x := v) (by decide : 0 ≤ 9)
      (PUnit.unit : BasedWalk (graph F) 0 v) (by trivial)
    let E := stabilizer F v ⊓ stabilizer F (p.1 : Vertex F)
    apply rootPathTransitive_of_odd_fixer_and_card F degree hval p hp
      (E.pCoreIn 2) (E.pCoreIn_le 2) _ (isPGroup_pCoreIn 2 E) (hodd p hp le_rfl).1
    rw [hB p.1.property,hfield]
    change q^12 = BasedWalk.forwardCount degree 8 (p.1 : Vertex F).type
    dsimp only [degree]
    cases i <;> cases (p.1 : Vertex F).type <;>
      norm_num only [BasedWalk.forwardCount,Bool.not_false,Bool.not_true,
        Bool.false_eq_true,Bool.true_eq_false,if_true,if_false,Nat.add_sub_cancel,mul_one] <;> ring
  have hs : sourceS (P := fun j => (P₀ L S j).subgroupOf (G₀ L S)) = 9 := le_antisymm
    (source_suzuki_sourceS_le_nine h i hb3 T hT e hz hcard hcardy hzy hcommy
      hcross hsmall hactor hn eSuz hfield Ry hRy hmin hnat hxadj hne hbranch)
    (sourceS_ge_of_root_transitive (reduced_triple h) (reduced_vertex_sylow h)
      (fun j => htrans (base F j)))
  refine ⟨hs,htrans,?_,hodd⟩
  intro r v p hp
  constructor
  · intro hr
    by_contra hnine
    have h9 : 9 ≤ r := by omega
    obtain ⟨r',rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    exact source_path_not_right_regular_of_odd h p (hodd p hp h9).1 hr.2
  · intro hr
    exact sourceS_short_regular (reduced_triple h) (reduced_vertex_sylow h) p (by omega) hp

/-- Source (12.9)(c)'s extrema r = 8 and s = 9, including the book's permitted closed paths. -/
theorem source_suzuki_source_path_parameters
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
    (hnear : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) x,
      V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥) :
    NoncommutingProfile.HasSourcePathParameters
      (P := fun j => (P₀ L S j).subgroupOf (G₀ L S)) 8 9 := by
  let F := reducedFamily L S
  obtain ⟨hs,_,hreg,_⟩ := source_suzuki_exact_path_parameter h i hb3 hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat hbranch hnear
  have hval (v : Vertex F) : 3 ≤ Nat.card ((graph F).neighborSet v) := by
    rw [card_neighbors_of_indices F (fun j => ((F (!j)).subgroupOf (F j)).index) (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) v.type
  have hdeg : HasTwoNeighbors (graph F) := by
    intro v w
    apply Set.exists_ne_of_one_lt_ncard (s := (graph F).neighborSet v) _ w
    rw [←Nat.card_coe_set_eq]
    exact lt_of_lt_of_le (by decide : 1 < 3) (hval v)
  obtain ⟨p,hp,_⟩ := BasedWalk.exists_extension hdeg (x := base F i) (by decide : 0 ≤ 8)
    (PUnit.unit : BasedWalk (graph F) 0 (base F i)) (by trivial)
  have hpath : p.toWalk.IsPath := isPath_of_short_rightRegular hval 9
    (fun r hr v t ht => (sourceS_short_regular (reduced_triple h) (reduced_vertex_sylow h)
      t (by omega) ht).2) p (by decide) hp
  constructor
  · refine ⟨⟨base F i,p.endpoint,p.toWalk,Or.inl hpath,length_toWalk p,
      (based_regular_iff p).mpr ((hreg p hp).mpr (by decide))⟩,?_⟩
    rintro r ⟨v,w,t,ht,htl,htr⟩
    by_cases hr : r ≤ 8
    · exact hr
    · have hnb := sourcePath_nonbacktracking t ht (by omega)
      have hh := (hreg (ofWalk t) hnb).mp ((walk_regular_iff t).mp htr)
      omega
  · have hh := (sourceS_spec (reduced_triple h) (reduced_vertex_sylow h)).2
    rw [hs] at hh
    exact hh

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
