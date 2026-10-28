module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSourceUpperBound
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiFullSecondKernel
public import Theory.GroupTheory.AmalgamGraph.OddPathOrderBound
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearValence
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration

/-!
# Geometric upper orders for the full Borel core

The literal original quotient markings give valences q+1 and q²+1.
A two-subgroup of an edge acts freely on the extensions of a nine-path,
whose fixer has odd order by (12.7). There are q¹² such extensions.
Conjugating the first edge back to the original edge and preserving the
reduced-to-original inclusion bounds the original full Borel two-core.
The actual neighboring core indices then give q¹¹ and q¹⁰ bounds for
the linear and Suzuki cores. The faithful q⁴ second-kernel quotient and
full-kernel containment finally give |G_beta^(2)| ≤ q⁶.

Source: DGS85, Groups and Graphs (1985), (12.7)--(12.9), pp.184--187.
Earlier source center, Sylow, commutator and marked-quotient inputs remain
explicit. No exact core order or full-kernel equality is assumed.
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped MatrixGroups Pointwise
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem marked_base_neighbor_index
    {M : Type*} [Group M] (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* M)
    (hloc : graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) = star L S i) :
    ∃ R : Sylow 2 M,
      ((reducedFamily L S (!i)).subgroupOf (reducedFamily L S i)).index =
        (normalizer (R : Set M)).index := by
  let F := reducedFamily L S
  let A := star L S i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer i)) (inclusion_injective _)
  let f := ((originalQuotient h i).symm.trans e).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := ((originalQuotient h i).symm.trans e).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 A := by
    ext t
    change e ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) t)) = 1 ↔ t ∈ pCore 2 A
    rw [map_eq_one_iff _ e.injective,map_eq_one_iff _ (originalQuotient h i).symm.injective]
    exact QuotientGroup.eq_one_iff t
  obtain ⟨T,hT⟩ := base_star_sylow_normalizer h i
  let R : Sylow 2 M := T.mapSurjective (f := f) hf
  have hRT : (R : Subgroup M).comap f = (T : Subgroup A) := by
    apply comap_map_eq_self
    rw [hk]
    exact pCore_isPGroup.le_sylow_of_normal T
  have hnorm : (normalizer (R : Set M)).comap f =
      (stabilizer F (base F (!i))).subgroupOf A := by
    change (normalizer ((R : Subgroup M) : Set M)).comap f = _
    rw [comap_normalizer_eq_of_surjective _ hf,hRT,Sylow.coe_coe,←hT]
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hi := source_edge_index_local (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hadj
  change (stabilizer F (base F (!i))).relIndex (stabilizer F (base F i)) =
    (stabilizer F (base F (!i))).relIndex (graphLocalGroup F (base F i)) at hi
  change graphLocalGroup F (base F i) = A at hloc
  rw [hloc] at hi
  refine ⟨R,?_⟩
  change (F (!i)).relIndex (F i) = _
  have he : (stabilizer F (base F (!i))).relIndex (stabilizer F (base F i)) =
      (normalizer (R : Set M)).index := by
    rw [hi]
    change ((stabilizer F (base F (!i))).subgroupOf A).index = _
    rw [←hnorm,index_comap_of_surjective _ hf]
  simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base] using he

/-- The literal linear/Suzuki markings determine both original graph valences. -/
theorem source_linear_suzuki_neighbor_cards
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ}
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hq : Nat.card k = 2^(2*n+1)) (v : Vertex (reducedFamily L S)) :
    Nat.card ((graph (reducedFamily L S)).neighborSet v) =
      if v.type = i then 2^(2*n+1)+1 else (2^(2*n+1))^2+1 := by
  let F := reducedFamily L S
  let ep : SL(2,k) ≃* BenderSuzuki.Converse.PSL2 k :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  obtain ⟨T,hT⟩ := marked_base_neighbor_index h i (eLin.trans ep)
    (source_linear_graphLocalGroup_eq_star h i eLin)
  have hi : ((F (!i)).subgroupOf (F i)).index = 2^(2*n+1)+1 :=
    hT.trans ((linear_sylow_normalizer_index T).trans (congrArg (·+1) hq))
  obtain ⟨R,hR⟩ := marked_base_neighbor_index h (!i) eSuz
    (source_suzuki_graphLocalGroup_eq_star h (!i) eSuz)
  have hj : ((F i).subgroupOf (F (!i))).index = (2^(2*n+1))^2+1 := by
    simpa only [Bool.not_not] using hR.trans (suzuki_sylow_normalizer_index n R)
  apply card_neighbors_of_indices F (fun j => if j = i then 2^(2*n+1)+1 else (2^(2*n+1))^2+1) _ v
  intro j
  by_cases hji : j = i
  · subst j
    rw [if_pos rfl]
    exact hi
  · have he : j = !i := Bool.eq_not_iff.mpr hji
    rw [if_neg hji,he,Bool.not_not]
    exact hj

set_option backward.isDefEq.respectTransparency false in
/-- The full original Borel two-core has order at most q¹² in the nonbinary source branch. -/
theorem source_suzuki_full_borel_core_upper
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {σ : Vertex (reducedFamily L S)}
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
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
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    {x₀ : Vertex (reducedFamily L S)}
    (hx₀ : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x₀)
    (hx₀n : x₀ ≠ base (reducedFamily L S) (!i))
    (hbranch : ⁅V (reducedFamily L S) x₀ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
 :
    Nat.card ((commonBorel L S).pCoreIn 2) ≤ (2^(2*n+1))^12 := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  obtain ⟨ℓ,_,j,δ,_,_,_,C,hoddC,_,_,_,_,v₀,p,hp,hm,hy,_,_,_⟩ :=
    source_mixed_minimal_path_fixed_nine_path h i hn e eSuz Ry hRy
  have ho := source_suzuki_every_nine_path_odd h i hb3 T hT e hz hcard hcardy
    hzy hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hmin hnat hx₀ hx₀n hbranch p hp
  let E := stabilizer F v₀ ⊓ stabilizer F (p.1 : Vertex F)
  have hbnd := two_subgroup_card_le_forwardCount_of_odd_fixer F
    (fun j => if j = i then 2^(2*n+1)+1 else (2^(2*n+1))^2+1)
    (source_linear_suzuki_neighbor_cards h i e eSuz hfield) p hp (E.pCoreIn 2)
    (pCoreIn_le 2 E) (isPGroup_pCoreIn 2 E) ho.1
  have hcount : BasedWalk.forwardCount
      (fun j => if j = i then 2^(2*n+1)+1 else (2^(2*n+1))^2+1)
      8 (p.1 : Vertex F).type = (2^(2*n+1))^12 := by
    cases i <;> cases (p.1 : Vertex F).type <;>
      norm_num only [BasedWalk.forwardCount,Bool.not_false,Bool.not_true,
        Bool.false_eq_true,Bool.true_eq_false,if_true,if_false,Nat.add_sub_cancel,mul_one] <;> ring
  rw [hcount] at hbnd
  obtain ⟨g,hg⟩ := edgeStabilizer_map_base F p.1.property
  have hE : E.pCoreIn 2 = ((F false ⊓ F true).pCoreIn 2).map (MulAut.conj g).toMonoidHom := by
    rw [show E = stabilizer F v₀ ⊓ stabilizer F (p.1 : Vertex F) from rfl,hg,
      Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (MulAut.conj g).injective]
  rw [hE,card_map_of_injective (MulAut.conj g).injective] at hbnd
  have hBG : B₀ L S ≤ G₀ L S :=
    (show B₀ L S ≤ P₀ L S 0 from le_sup_right).trans le_sup_left
  have hcore : (((B₀ L S).subgroupOf (G₀ L S)).pCoreIn 2).map (G₀ L S).subtype =
      (commonBorel L S).pCoreIn 2 := by
    rw [←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (G₀ L S).subtype_injective,
      map_subgroupOf_eq_of_le hBG,B₀_core h]
  rw [←hcore,card_map_of_injective (G₀ L S).subtype_injective]
  have hint : F false ⊓ F true = (B₀ L S).subgroupOf (G₀ L S) := (reduced_triple h).intersection
  rwa [hint] at hbnd

set_option backward.isDefEq.respectTransparency false in
/-- The original neighboring core indices turn the full-Borel bound into
q¹¹ and q¹⁰ upper bounds for the linear and Suzuki cores, respectively. -/
theorem source_suzuki_vertex_core_upper
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {σ : Vertex (reducedFamily L S)}
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
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
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    {x₀ : Vertex (reducedFamily L S)}
    (hx₀ : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x₀)
    (hx₀n : x₀ ≠ base (reducedFamily L S) (!i))
    (hbranch : ⁅V (reducedFamily L S) x₀ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)
 :
    let F := reducedFamily L S
    Nat.card (Q F (base F i)) ≤ (2^(2*n+1))^11 ∧
    Nat.card (Q F (base F (!i))) ≤ (2^(2*n+1))^10 ∧
    Nat.card ((Q F (base F i)).map (G₀ L S).subtype) ≤ (2^(2*n+1))^11 ∧
    Nat.card ((Q F (base F (!i))).map (G₀ L S).subtype) ≤ (2^(2*n+1))^10 := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let J := Q F y ⊔ Q F m
  let E := stabilizer F m ⊓ stabilizer F y
  let q := 2^(2*n+1)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite E := Finite.of_injective
    (inclusion (show E ≤ stabilizer F m from inf_le_left)) (inclusion_injective _)
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hQym : Q F y ≤ stabilizer F m :=
    ((source_Z_Q_U (reduced_triple h) y).2.trans (ballKernel_one_le_edge F hadj.symm)).trans inf_le_right
  have hQmy : Q F m ≤ stabilizer F y :=
    ((source_Z_Q_U (reduced_triple h) m).2.trans (ballKernel_one_le_edge F hadj)).trans inf_le_right
  have hJE : J ≤ E := sup_le (le_inf hQym (Q_le_stabilizer F y))
    (le_inf (Q_le_stabilizer F m) hQmy)
  have hpJ : IsPGroup 2 J := by
    change IsPGroup 2 (Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
      Q (reducedFamily L S) (base (reducedFamily L S) i) : Subgroup (G₀ L S))
    rw [←hT]
    exact T.isPGroup'.map (star L S i).subtype
  have hJcore : J ≤ E.pCoreIn 2 := pGroup_le_core_of_core_sylow E J hJE hpJ
    (source_edge_core_sylow (reduced_triple h) (reduced_borel_core_sylow h) hadj)
  let : Finite J := Finite.of_injective (inclusion hJE) (inclusion_injective _)
  let : Finite (Q F m) := Finite.of_injective (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  let : Finite (Q F y) := Finite.of_injective (inclusion (Q_le_stabilizer F y)) (inclusion_injective _)
  let : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E)) (inclusion_injective _)
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
  have hB := source_suzuki_full_borel_core_upper h i hb3 T hT e hz hcard hcardy
    hzy hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hmin hnat hx₀ hx₀n hbranch
  have hJ : Nat.card J ≤ q^12 := by
    apply (Nat.card_le_card_of_injective (inclusion hJcore) (inclusion_injective _)).trans
    rw [←hcore,card_map_of_injective (G₀ L S).subtype_injective] at hB
    exact hB
  obtain ⟨U,_,hiLin,_⟩ := source_common_sylow_core_index h i e T hT
  have hiL : (Q F y ⊓ Q F m).relIndex (Q F y) = q :=
    hiLin.trans ((Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 U).symm.toEquiv).trans hfield)
  obtain ⟨R,_,hiSuz,_⟩ := source_common_sylow_core_index h (!i) eSuz Ry hRy
  have hiS : (Q F m ⊓ Q F y).relIndex (Q F m) = q^2 :=
    hiSuz.trans (suzukiSylow_card hn (MulEquiv.refl _) R)
  have hmJ : (Q F m).relIndex J = q := by
    rw [show J = Q F y ⊔ Q F m from rfl,relIndex_sup_of_normalizes _ _
      (hQmy.trans (CommutingTrivial.stabilizer_normalizes_Q F y))]
    rwa [inf_relIndex_left] at hiL
  have hyJ : (Q F y).relIndex J = q^2 := by
    rw [show J = Q F m ⊔ Q F y from sup_comm _ _,relIndex_sup_of_normalizes _ _
      (hQym.trans (CommutingTrivial.stabilizer_normalizes_Q F m))]
    rwa [inf_relIndex_left] at hiS
  have hcm := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) (Q F m) J bot_le le_sup_right
  rw [relIndex_bot_left,relIndex_bot_left,hmJ] at hcm
  have hcy := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) (Q F y) J bot_le le_sup_left
  rw [relIndex_bot_left,relIndex_bot_left,hyJ] at hcy
  have hmcard : Nat.card (Q F m) ≤ q^11 := by
    apply Nat.le_of_mul_le_mul_right (c := q) _ (by positivity)
    calc
      Nat.card (Q F m) * q = Nat.card J := hcm
      _ ≤ q^12 := hJ
      _ = q^11*q := by ring
  have hycard : Nat.card (Q F y) ≤ q^10 := by
    apply Nat.le_of_mul_le_mul_right (c := q^2) _ (by positivity)
    calc
      Nat.card (Q F y) * q^2 = Nat.card J := hcy
      _ ≤ q^12 := hJ
      _ = q^10*q^2 := by ring
  refine ⟨hmcard,hycard,?_,?_⟩
  · rw [card_map_of_injective (G₀ L S).subtype_injective]
    exact hmcard
  · rw [card_map_of_injective (G₀ L S).subtype_injective]
    exact hycard

set_option backward.isDefEq.respectTransparency false in
/-- The full Suzuki second kernel has order at most q⁶; the denominator
is the full ball kernel, and its original inclusion is preserved. -/
theorem source_suzuki_full_second_kernel_upper
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {σ : Vertex (reducedFamily L S)}
    (T : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
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
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    {x₀ : Vertex (reducedFamily L S)}
    (hx₀ : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x₀)
    (hx₀n : x₀ ≠ base (reducedFamily L S) (!i))
    (hbranch : ⁅V (reducedFamily L S) x₀ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥)

    (hfull : V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 =
      ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1, star L S (!i)⁆) :
    let F := reducedFamily L S
    Nat.card (ballKernel F (base F (!i)) 2) ≤ (2^(2*n+1))^6 ∧
    Nat.card ((ballKernel F (base F (!i)) 2).map (G₀ L S).subtype) ≤ (2^(2*n+1))^6 := by
  let F := reducedFamily L S
  let y := base F (!i)
  let N := ballKernel F y 2
  let q := 2^(2*n+1)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite (Q F y) := Finite.of_injective (inclusion (Q_le_stabilizer F y)) (inclusion_injective _)
  have hk : 4 ≤ Nat.card k := by
    rw [hfield]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ 2*n+1)
  have hN : N ≤ Q F y := source_suzuki_second_kernel_le_core h (!i) eSuz
    (by cases i <;> exact e) hk y
  let : Finite N := Finite.of_injective (inclusion hN) (inclusion_injective _)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  obtain ⟨ρ,hρ,hi,_⟩ := source_suzuki_second_kernel_faithful h (!i) hb eSuz
    (by cases i <;> exact T) (by cases i <;> exact hT)
    Ry (by cases i <;> exact hRy) (by cases i <;> exact hnat) (by cases i <;> exact hzy)
    hcommy hfull
  have hQ := (source_suzuki_vertex_core_upper h i hb3 T hT e hz hcard hcardy
    hzy hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hmin hnat hx₀ hx₀n hbranch).2.1
  have hm := relIndex_mul_relIndex (⊥ : Subgroup (G₀ L S)) N (Q F y) bot_le hN
  rw [relIndex_bot_left,relIndex_bot_left] at hm
  have hc : Nat.card N ≤ q^6 := by
    apply Nat.le_of_mul_le_mul_right (c := q^4) _ (by positivity)
    calc
      Nat.card N * q^4 ≤ Nat.card N * N.relIndex (Q F y) := Nat.mul_le_mul_left _ hi
      _ = Nat.card (Q F y) := hm
      _ ≤ q^10 := hQ
      _ = q^6*q^4 := by ring
  refine ⟨hc,?_⟩
  rw [card_map_of_injective (G₀ L S).subtype_injective]
  exact hc

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
