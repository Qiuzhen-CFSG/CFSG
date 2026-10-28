module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.AdaptedCoreElementary

public import Theory.GroupTheory.Hall.OddNormalProducts
public import Theory.GroupTheory.AmalgamGraph.NormalTwoDetection
public import Theory.ElementaryAbelian.Join
public import Theory.ElementaryAbelian.Injective
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicCentralNeighbors

/-!
# The product of the two adapted factors

At the middle vertex x of beta—x—d, the two adapted factors generate a
subgroup M of Q_x normalized by the whole local group. Their intersection
is normal there and misses the actual Sylow-center span, so it is trivial.
The adjacent-core index gives order q² for each factor, hence |M| = q⁴.
The original reduced-graph application supplies the core escapes and the
disjointness of the neighboring center subgroups.

Source: DGS, *Groups and Graphs* (1985), printed p.150, the construction of M
in the proof of 9.10. The adapted elementary factors come from the natural
self-extension argument and its central-cover calculation.
-/

public noncomputable section
open Subgroup Representation
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

theorem adapted_pair_normality
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {x beta d : Vertex (family P)}
    (hb : (graph (family P)).Adj x beta) (hd : (graph (family P)).Adj x d)
    (hne : beta ≠ d) (hbesc : ¬ Q (family P) beta ≤ Q (family P) x)
    (hdesc : ¬ Q (family P) d ≤ Q (family P) x)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (ex : (graphLocalGroup (family P) x ⧸ pCore 2 (graphLocalGroup (family P) x)) ≃* SL(2,F))
    (Wb Wd : Subgroup G) (hWb : Wb ≤ Q (family P) beta) (hWd : Wd ≤ Q (family P) d)
    (hnb : graphLocalGroup (family P) beta ≤ normalizer (Wb : Set G))
    (hnd : graphLocalGroup (family P) d ≤ normalizer (Wd : Set G))
    (hspb : Wb ⊔ V (family P) beta 1 = Q (family P) beta)
    (hspd : Wd ⊔ V (family P) d 1 = Q (family P) d)
    (hVb : V (family P) beta 1 ≤ Q (family P) x)
    (hVd : V (family P) d 1 ≤ Q (family P) x) :
    let M := (Wb ⊓ Q (family P) x) ⊔ (Wd ⊓ Q (family P) x)
    M ≤ Q (family P) x ∧
      graphLocalGroup (family P) x ≤ normalizer (M : Set G) ∧
      ⁅M,Wb⁆ ≤ Wb ⊓ Q (family P) x ∧ ⁅M,Wd⁆ ≤ Wd ⊓ Q (family P) x := by
  let Γ := family P
  let R := Q Γ x
  let M := (Wb ⊓ R) ⊔ (Wd ⊓ R)
  have hMR : M ≤ R := sup_le inf_le_right inf_le_right
  have hRN : graphLocalGroup Γ x ≤ normalizer (R : Set G) :=
    (sylowGenerated_le _).trans (stabilizer_normalizes_Q Γ x)
  have hRb : R ≤ normalizer (Wb : Set G) :=
    (neighbor_core_le_localGroup h hB hS hb.symm).trans hnb
  have hRd : R ≤ normalizer (Wd : Set G) :=
    (neighbor_core_le_localGroup h hB hS hd.symm).trans hnd
  have hbR : Wb ≤ normalizer (R : Set G) :=
    (hWb.trans (neighbor_core_le_localGroup h hB hS hb)).trans hRN
  have hdR : Wd ≤ normalizer (R : Set G) :=
    (hWd.trans (neighbor_core_le_localGroup h hB hS hd)).trans hRN
  have hRM : R ≤ normalizer (M : Set G) := by
    apply (le_inf ?_ ?_).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact (le_inf hRb R.le_normalizer).trans inf_normalizer_le_normalizer_inf
    · exact (le_inf hRd R.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hcb : ⁅M,Wb⁆ ≤ Wb ⊓ R := le_inf
    (le_normalizer_iff_commutator_le_right.mp (hMR.trans hRb))
    ((commutator_mono hMR le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hbR))
  have hcd : ⁅M,Wd⁆ ≤ Wd ⊓ R := le_inf
    (le_normalizer_iff_commutator_le_right.mp (hMR.trans hRd))
    ((commutator_mono hMR le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hdR))
  have hbM : Wb ≤ normalizer (M : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hcb.trans le_sup_left)
  have hdM : Wd ≤ normalizer (M : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hcd.trans le_sup_right)
  refine ⟨hMR,?_,hcb,hcd⟩
  rw [linear_neighbor_core_generation h hB hS hb hd hne hbesc hdesc ex]
  exact sup_le (sup_le hRM (hspb ▸ sup_le hbM (hVb.trans hRM)))
    (hspd ▸ sup_le hdM (hVd.trans hRM))

/-- The natural adapted factor has a q² intersection with the neighboring core;
that intersection cannot lie in its old natural span. -/
theorem adapted_core_intersection_order
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {x d : Vertex (family P)} (hd : (graph (family P)).Adj x d)
    (hdesc : ¬ Q (family P) d ≤ Q (family P) x)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (ex : (graphLocalGroup (family P) x ⧸ pCore 2 (graphLocalGroup (family P) x)) ≃* SL(2,F))
    (W : Subgroup G) (hW : W ≤ Q (family P) d)
    (hWV : W ⊓ V (family P) d 1 = Z (family P) d)
    (hsp : W ⊔ V (family P) d 1 = Q (family P) d)
    (hV : V (family P) d 1 ≤ Q (family P) x)
    (hWcard : Nat.card W = Nat.card F ^ 3)
    (hZcard : Nat.card (Z (family P) d) = Nat.card F) :
    Nat.card (W ⊓ Q (family P) x : Subgroup G) = Nat.card F ^ 2 ∧
      ¬ W ⊓ Q (family P) x ≤ V (family P) d 1 := by
  let := finite_endpoints h
  let Γ := family P
  let R := Q Γ x
  have hnorm : Q Γ d ≤ normalizer (R : Set G) :=
    ((neighbor_core_le_localGroup h hB hS hd).trans (sylowGenerated_le _)).trans
      (stabilizer_normalizes_Q Γ x)
  have hsup : R ⊔ Q Γ d = R ⊔ W := by
    apply le_antisymm
    · exact sup_le le_sup_left (hsp ▸ sup_le le_sup_right (hV.trans le_sup_left))
    · exact sup_le le_sup_left (hW.trans le_sup_right)
  have hi : R.relIndex W = Nat.card F := by
    rw [←OddHall.relIndex_normalized_sup R W (hW.trans hnorm),←hsup,
      OddHall.relIndex_normalized_sup R (Q Γ d) hnorm]
    exact linear_adjacent_core_index h hB hS hd hdesc ex
  let : Finite (Q Γ d) := Finite.of_injective (inclusion (Q_le_stabilizer Γ d))
    (inclusion_injective _)
  let : Finite (Z Γ d) := Finite.of_injective (inclusion (Z_le_stabilizer Γ d))
    (inclusion_injective _)
  let : Finite W := Finite.of_injective (inclusion hW) (inclusion_injective _)
  let : Finite (W ⊓ R : Subgroup G) := Finite.of_injective (inclusion inf_le_left)
    (inclusion_injective _)
  have hcard : Nat.card (W ⊓ R : Subgroup G) = Nat.card F ^ 2 := by
    have hh := relIndex_mul_card_of_le (show W ⊓ R ≤ W from inf_le_left)
    rw [inf_relIndex_left,hi,hWcard] at hh
    have hp : 0 < Nat.card F := Nat.card_pos
    nlinarith
  refine ⟨hcard,?_⟩
  intro hc
  have hz : W ⊓ R ≤ Z Γ d := hWV ▸ le_inf inf_le_left hc
  have hle := Nat.card_le_card_of_injective (inclusion hz) (inclusion_injective hz)
  rw [hcard,hZcard] at hle
  have hp : 1 < Nat.card F := Finite.one_lt_card
  nlinarith


/-- Two abelian adapted factors have disjoint intersections in the middle core.
The common intersection is normal in the whole middle local group and misses
its actual Sylow-center span. -/
theorem adapted_pair_disjoint
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {x beta d : Vertex (family P)}
    (hb : (graph (family P)).Adj x beta) (hd : (graph (family P)).Adj x d)
    (hne : beta ≠ d) (hbesc : ¬ Q (family P) beta ≤ Q (family P) x)
    (hdesc : ¬ Q (family P) d ≤ Q (family P) x)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (ex : (graphLocalGroup (family P) x ⧸ pCore 2 (graphLocalGroup (family P) x)) ≃* SL(2,F))
    (Wb Wd : Subgroup G) [IsMulCommutative Wb] [IsMulCommutative Wd]
    (hnb : graphLocalGroup (family P) beta ≤ normalizer (Wb : Set G))
    (hnd : graphLocalGroup (family P) d ≤ normalizer (Wd : Set G))
    (hspb : Wb ⊔ V (family P) beta 1 = Q (family P) beta)
    (hspd : Wd ⊔ V (family P) d 1 = Q (family P) d)
    (hVb : V (family P) beta 1 ≤ Q (family P) x)
    (hVd : V (family P) d 1 ≤ Q (family P) x)
    (hWVb : Wb ⊓ V (family P) beta 1 = Z (family P) beta)
    (hWVd : Wd ⊓ V (family P) d 1 = Z (family P) d)
    (hZdis : Disjoint (Z (family P) beta) (Z (family P) d)) :
    Disjoint (Wb ⊓ Q (family P) x) (Wd ⊓ Q (family P) x) := by
  let Γ := family P
  let : ∀ i, Finite (Γ i) := finite_endpoints h
  let R := Q Γ x
  let J := graphLocalGroup Γ x
  let I := Wb ⊓ Wd ⊓ R
  let : Finite J := Finite.of_injective (inclusion (sylowGenerated_le _))
    (inclusion_injective _)
  have hRb : R ≤ normalizer (Wb : Set G) :=
    (neighbor_core_le_localGroup h hB hS hb.symm).trans hnb
  have hRd : R ≤ normalizer (Wd : Set G) :=
    (neighbor_core_le_localGroup h hB hS hd.symm).trans hnd
  have hRI : R ≤ normalizer (I : Set G) :=
    (le_inf ((le_inf hRb hRd).trans inf_normalizer_le_normalizer_inf) R.le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hbI : Wb ≤ normalizer (I : Set G) :=
    ((le_centralizer Wb).trans (centralizer_le (inf_le_left.trans inf_le_left))).trans
      (centralizer_le_normalizer _)
  have hdI : Wd ≤ normalizer (I : Set G) :=
    ((le_centralizer Wd).trans (centralizer_le (inf_le_left.trans inf_le_right))).trans
      (centralizer_le_normalizer _)
  have hJI : J ≤ normalizer (I : Set G) := by
    change graphLocalGroup Γ x ≤ _
    rw [linear_neighbor_core_generation h hB hS hb hd hne hbesc hdesc ex]
    exact sup_le (sup_le hRI (hspb ▸ sup_le hbI (hVb.trans hRI)))
      (hspd ▸ sup_le hdI (hVd.trans hRI))
  have hIZ : Disjoint I (sylowCenterSpan J) := by
    rw [←graph_intrinsic_center_span h x]
    apply disjoint_def.mpr
    intro z hz hzZ
    have hzb : z ∈ Z Γ beta := hWVb ▸
      (show z ∈ Wb ⊓ V Γ beta 1 from
        ⟨hz.1.1,CommutingNontrivial.Z_neighbor_le_V Γ hb.symm hzZ⟩)
    have hzd : z ∈ Z Γ d := hWVd ▸
      (show z ∈ Wd ⊓ V Γ d 1 from
        ⟨hz.1.2,CommutingNontrivial.Z_neighbor_le_V Γ hd.symm hzZ⟩)
    exact disjoint_def.mp hZdis hzb hzd
  have hIbot : I = ⊥ := normal_two_eq_bot_of_disjoint_sylowCenterSpan J I
    (inf_le_right.trans (core_le_graphLocalGroup h x))
    ((isPGroup_pCoreIn 2 _).to_le inf_le_right) hJI hIZ
  apply disjoint_def.mpr
  intro z hzb hzd
  have hz : z ∈ I := ⟨⟨hzb.1,hzd.1⟩,hzb.2⟩
  rwa [hIbot,mem_bot] at hz


variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The page-150 product in the original reduced graph is elementary, normal
in L_x, and has order q⁴. Its two factors and their escape are retained. -/
theorem reduced_adapted_pair_order
    (h : HypothesisF11 L S)
    {x beta d : Vertex (Reduction.reducedFamily L S)}
    (hb : (graph (Reduction.reducedFamily L S)).Adj x beta)
    (hd : (graph (Reduction.reducedFamily L S)).Adj x d) (hne : beta ≠ d)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (ex : (graphLocalGroup (Reduction.reducedFamily L S) x ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S) x)) ≃* SL(2,F))
    (Wb Wd : Subgroup (Reduction.G₀ L S))
    [IsElementaryAbelian 2 Wb] [IsElementaryAbelian 2 Wd]
    (hnb : graphLocalGroup (Reduction.reducedFamily L S) beta ≤ normalizer (Wb : Set (Reduction.G₀ L S)))
    (hnd : graphLocalGroup (Reduction.reducedFamily L S) d ≤ normalizer (Wd : Set (Reduction.G₀ L S)))
    (hspb : Wb ⊔ V (Reduction.reducedFamily L S) beta 1 = Q (Reduction.reducedFamily L S) beta)
    (hspd : Wd ⊔ V (Reduction.reducedFamily L S) d 1 = Q (Reduction.reducedFamily L S) d)
    (hVb : V (Reduction.reducedFamily L S) beta 1 ≤ Q (Reduction.reducedFamily L S) x)
    (hVd : V (Reduction.reducedFamily L S) d 1 ≤ Q (Reduction.reducedFamily L S) x)
    (hWVb : Wb ⊓ V (Reduction.reducedFamily L S) beta 1 = Z (Reduction.reducedFamily L S) beta)
    (hWVd : Wd ⊓ V (Reduction.reducedFamily L S) d 1 = Z (Reduction.reducedFamily L S) d)
    (hω : Z (Reduction.reducedFamily L S) beta =
      omegaCenterIn (graphLocalGroup (Reduction.reducedFamily L S) beta))
    (hZcard : Nat.card (Z (Reduction.reducedFamily L S) beta) = Nat.card F)
    (hWbcard : Nat.card Wb = Nat.card F ^ 3) (hWdcard : Nat.card Wd = Nat.card F ^ 3) :
    let Γ := Reduction.reducedFamily L S
    let M := (Wb ⊓ Q Γ x) ⊔ (Wd ⊓ Q Γ x)
    M ≤ Q Γ x ∧ graphLocalGroup Γ x ≤ normalizer (M : Set (Reduction.G₀ L S)) ∧
      IsElementaryAbelian 2 M ∧ Nat.card M = Nat.card F ^ 4 ∧
      Disjoint (Wb ⊓ Q Γ x) (Wd ⊓ Q Γ x) ∧
      (¬ Wb ⊓ Q Γ x ≤ V Γ beta 1) ∧ (¬ Wd ⊓ Q Γ x ≤ V Γ d 1) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hB := Reduction.reduced_borel_core_sylow h
  have hS := Reduction.reduced_vertex_sylow h
  have hWb : Wb ≤ Q Γ beta := hspb ▸ le_sup_left
  have hWd : Wd ≤ Q Γ d := hspd ▸ le_sup_left
  have hbesc : ¬ Q Γ beta ≤ Q Γ x := core_escape_of_intersection_obstruction Γ
    (Reduction.reduced_graph_core_obstruction h beta x hb.symm)
  have hdesc : ¬ Q Γ d ≤ Q Γ x := core_escape_of_intersection_obstruction Γ
    (Reduction.reduced_graph_core_obstruction h d x hd.symm)
  have hZdis := Reduction.reduced_intrinsic_central_neighbor_centers_disjoint h hb hd hne hω
  have hdis := adapted_pair_disjoint ht hB hS hb hd hne hbesc hdesc ex
    Wb Wd hnb hnd hspb hspd hVb hVd hWVb hWVd hZdis
  obtain ⟨hMR,hMN,_,_⟩ := adapted_pair_normality ht hB hS hb hd hne hbesc hdesc ex
    Wb Wd hWb hWd hnb hnd hspb hspd hVb hVd
  have hZcardd : Nat.card (Z Γ d) = Nat.card F := by
    obtain ⟨g,_,hg⟩ := locally_transitive Γ hb hd
    rw [←hg,Z_translate,card_map_of_injective (MulAut.conj g).injective]
    exact hZcard
  obtain ⟨hAb,hAesc⟩ := adapted_core_intersection_order ht hB hS hb hbesc ex Wb
    hWb hWVb hspb hVb hWbcard hZcard
  obtain ⟨hAd,hDesc⟩ := adapted_core_intersection_order ht hB hS hd hdesc ex Wd
    hWd hWVd hspd hVd hWdcard hZcardd
  let A := Wb ⊓ Q Γ x
  let D := Wd ⊓ Q Γ x
  change Nat.card A = Nat.card F ^ 2 at hAb
  change Nat.card D = Nat.card F ^ 2 at hAd
  have hnA : Q Γ x ≤ normalizer (A : Set (Reduction.G₀ L S)) :=
    (le_inf ((neighbor_core_le_localGroup ht hB hS hb.symm).trans hnb)
      (Q Γ x).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hnD : Q Γ x ≤ normalizer (D : Set (Reduction.G₀ L S)) :=
    (le_inf ((neighbor_core_le_localGroup ht hB hS hd.symm).trans hnd)
      (Q Γ x).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hc : ⁅D,A⁆ = ⊥ := bot_unique ((le_inf
    (le_normalizer_iff_commutator_le_right.mp (inf_le_right.trans hnA))
    (le_normalizer_iff_commutator_le_left.mp (inf_le_right.trans hnD))).trans hdis.le_bot)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
    (inclusion (show A ≤ Wb from inf_le_left)) (inclusion_injective _)
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_injective
    (inclusion (show D ≤ Wd from inf_le_left)) (inclusion_injective _)
  refine ⟨hMR,hMN,IsElementaryAbelian.sup_of_le_centralizer
    (commutator_eq_bot_iff_le_centralizer.mp hc),?_,hdis,hAesc,hDesc⟩
  rw [card_sup_eq_mul_of_normalizes_of_disjoint A D (inf_le_right.trans hnA) hdis,hAb,hAd]
  ring

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
