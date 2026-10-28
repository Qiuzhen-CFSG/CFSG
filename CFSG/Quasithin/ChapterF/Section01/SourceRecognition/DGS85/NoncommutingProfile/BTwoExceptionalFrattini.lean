module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoResidualSeparation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalCubic
public import Theory.GroupTheory.CommutatorPreimageFrattini
public import Theory.Representation.BinaryConjugationSection.FixedSplitting

/-!
# The exceptional alpha core is not elementary and has Frattini subgroup Z

If the alpha core were elementary abelian, its intersection with the
critical partner core would lie in the central involutions of the common
edge Sylow, hence in the middle center. Centrality of the beta center gives
the reverse inclusion. The two critical Sylow products then express the
beta core as the join of the critical centers. The earlier natural action
computes its order as q_alpha cubed. In the exceptional linear-beta branch,
the established order is q_alpha cubed times q_beta, a contradiction.

The elementary alpha-core quotient puts its Frattini subgroup inside
Z_alpha. Non-elementarity makes it nontrivial; the natural center action
is irreducible, so Phi(Q_alpha) = Z_alpha. This does not yet force
q_alpha = 2 or recognize either exceptional parabolic pair.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (10.9), printed p.163, using (10.1)--(10.2) and (10.7).
BTwoExceptionalFrattiniSource applies this to the original full cores.
-/

public noncomputable section
open Subgroup Representation Representation.RankOne.QuadraticRecognition
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local instance elementaryAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

private theorem elementary_critical_core_le_middle
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w : Vertex F}
    (hm : (graph F).Adj v m) (hw : (graph F).Adj m w)
    (hs : Stellmacher.IsSylowSubgroupIn (Z F v ⊔ Q F w) (stabilizer F w))
    [IsElementaryAbelian 2 (Q F w)] :
    Q F v ⊓ Q F w ≤ Z F m := by
  let := finite_endpoints h
  have hS := source_kernel_sylow h hB hSyl
  let S := Z F v ⊔ Q F w
  obtain ⟨T,hT⟩ := hs
  have hSE : S ≤ stabilizer F w ⊓ stabilizer F m := by
    apply sup_le
    · exact le_inf
        (Z_le_stabilizer_of_dist_le_b F h.generate v w (by
          have hh := (connected_graph h).dist_triangle (u := v) (v := m) (w := w)
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr hm,
            SimpleGraph.dist_eq_one_iff_adj.mpr hw] at hh
          simpa only [hb] using hh))
        ((graph_Z_le_Q_of_short h hS (by
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr hm,hb]; decide)).trans
          (Q_le_stabilizer F m))
    · exact le_inf (Q_le_stabilizer F w)
        ((source_Z_Q_U h w).2.trans
          ((ballKernel_one_le_edge F hw.symm).trans inf_le_right))
  have hedge : S = (stabilizer F w ⊓ stabilizer F m).pCoreIn 2 :=
    hT.symm.trans (sylow_image_eq_edge_core _ _ inf_le_left
      (source_edge_core_sylow h hB hw.symm) T (hT ▸ hSE))
  obtain ⟨A,hA⟩ := source_edge_vertex_sylow h hSyl hw
  have hAS : (A : Subgroup (stabilizer F m)).map (stabilizer F m).subtype = S := by
    rw [hedge]
    simpa only [inf_comm] using sylow_image_eq_edge_core _ _ inf_le_left
      (source_edge_core_sylow h hB hw) A hA
  have hseed : omegaCenterIn S ≤ Z F m := by
    rw [←hAS]
    exact le_iSup (fun R : Sylow 2 (stabilizer F m) =>
      omegaCenterIn ((R : Subgroup (stabilizer F m)).map (stabilizer F m).subtype)) A
  intro x hx
  apply hseed
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨mem_sup_right hx.2,?_,elemPow_eq_one_of_isElementaryAbelian x hx.2⟩
  have hZ : Z F v ≤ centralizer ({x} : Set G) := by
    intro z hz
    exact mem_centralizer_singleton_iff.mpr (graph_Q_centralizes_Z h v hx.1 z hz)
  have hQ : Q F w ≤ centralizer ({x} : Set G) := by
    intro z hz
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm (⟨z,hz⟩ : Q F w) ⟨x,hx.2⟩)
  intro z hz
  exact mem_centralizer_singleton_iff.mp ((sup_le hZ hQ) hz)

/-- An elementary alpha core meets its critical partner core in the middle center. -/
theorem BTwoCenterActionData.elementary_critical_core_intersection
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    [IsElementaryAbelian 2 (Q F v)] : Q F v ⊓ Q F w = Z F m := by
  have hle : Q F v ⊓ Q F w ≤ Z F m := by
    rw [inf_comm]
    exact elementary_critical_core_le_middle h hB hSyl hb c.terminal.symm c.middle.symm
      (c.own_critical_product h)
  have hzQ (x : Vertex F) : Z F x ≤ Q F x := fun _ hx =>
    ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h x).1 hx)).1
  exact le_antisymm hle (le_inf
    ((center_le_of_central_neighbor h hB hSyl c.middle hcentral).trans (hzQ v))
    ((center_le_of_central_neighbor h hB hSyl c.terminal.symm hcentral).trans (hzQ w)))

/-- The critical Sylow products force the beta-core order if the alpha core is elementary. -/
theorem BTwoCenterActionData.elementary_middle_core_card
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) [IsElementaryAbelian 2 (Q F v)] :
    Nat.card (Q F m) = Nat.card k ^ 3 := by
  let := finite_endpoints h
  have hS := source_kernel_sylow h hB hSyl
  have hzQ (x : Vertex F) : Z F x ≤ Q F x := fun _ hx =>
    ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h x).1 hx)).1
  have hi := c.elementary_critical_core_intersection h hB hSyl hb hcentral
  have hD : D F w v = Z F m := by
    change Q F w ⊓ Q F v = Z F m
    rwa [inf_comm]
  have hspan : Q F m = Z F v ⊔ Z F w := by
    rw [bTwo_core_span_of_sylow_products h hS hb c.middle c.terminal
      c.critical_product (c.own_critical_product h) (hD ▸ hzQ m),hD]
    rw [sup_eq_left.mpr ((center_le_of_central_neighbor h hB hSyl c.middle hcentral).trans
      le_sup_right),sup_comm]
  let : Finite (Z F w) := Finite.of_injective
    (inclusion (Z_le_stabilizer F w)) (inclusion_injective _)
  have hzw : Nat.card (Z F w) = Nat.card k ^ 2 := by
    obtain ⟨g,hg,he⟩ := locally_transitive F c.middle.symm c.terminal
    have hmap : (Z F v).map (MulAut.conj g).toMonoidHom = Z F w := by
      rw [←Z_translate,he]
    rw [←hmap,←Nat.card_congr ((Z F v).equivMapOfInjective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv]
    exact c.central_center_card E (c.omega_eq_bot_of_central_neighbor h hB hSyl hactor hcentral)
  have hn : Z F w ≤ normalizer (Z F v : Set G) :=
    (graph_Z_le_Q_of_short h hS (by
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr c.terminal.symm,hb]; decide)).trans
      ((c.neighbor_core_le.trans c.actor_le).trans
        ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F v)).mp (Z_normal F v)))
  have hidx : (Z F w).relIndex (Q F m) = Nat.card k := by
    rw [hspan,relIndex_sup_of_normalizes _ _ hn]
    have hh := c.central_critical_intersections h hB hSyl hb hcentral
    rw [←inf_relIndex_left,hh.2.2,←hh.1,inf_relIndex_left]
    exact c.line_index E
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (Z F w) (Q F m) bot_le
    (hspan ▸ le_sup_right)
  simp only [relIndex_bot_left,hidx,hzw] at hh
  rw [←hh]
  ring

/-- The beta-core order contradicts an elementary alpha core in the exceptional branch. -/
theorem BTwoCenterActionData.exceptional_linear_core_not_elementary
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K))
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    ¬ IsElementaryAbelian 2 (Q F v) := by
  intro he
  let := he
  have hc := c.elementary_middle_core_card h hB hSyl hb hactor hcentral E
  have ho := (c.exceptional_linear_core_orders h hB hSyl hb hactor hcentral ht hne
    hcomm hnot eβ hD E).2
  have hq : Nat.card K = 1 := by
    apply Nat.mul_left_cancel (pow_pos (Nat.card_pos : 0 < Nat.card k) 3)
    simpa only [mul_one] using ho.symm.trans hc
  have hk : 1 < Nat.card K := by
    let := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  omega

private theorem center_representation_irreducible
    {v m w : Vertex F} (c : BTwoCenterActionData F v m w k W)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) : c.representation.IsIrreducible := by
  let : Finite W := Finite.of_injective E E.injective
  obtain ⟨n,e,he⟩ := sl2_natural_copies c.representation c.imageSylow c.quadratic
    c.generated c.fixed_bot
  have hc := (Nat.card_congr E.toEquiv).symm.trans (Nat.card_congr e.toEquiv)
  simp only [Nat.card_fun,Nat.card_fin] at hc
  have hk : 1 < Nat.card k := by
    let := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hn : n = 1 := by
    rw [←pow_mul] at hc
    have hh := Nat.pow_right_injective hk hc
    omega
  subst n
  apply irreducible_of_natural_coordinates c.representation
    (e.trans (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Fin 2 → k)))
  intro g x
  exact he g x 0

/-- The literal alpha Frattini image is the natural center in the exceptional branch. -/
theorem BTwoCenterActionData.exceptional_linear_frattini
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K))
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    (frattini (Q F v)).map (Q F v).subtype = Z F v := by
  let := finite_endpoints h
  let : Finite (Q F v) := Finite.of_injective
    (inclusion (Q_le_stabilizer F v)) (inclusion_injective _)
  let : Fact (IsPGroup 2 (Q F v)) := ⟨isPGroup_pCoreIn 2 (stabilizer F v)⟩
  have hω := c.omega_eq_bot_of_central_neighbor h hB hSyl hactor hcentral
  let J := (frattini (Q F v)).map (Q F v).subtype
  have hJZ : J ≤ Z F v := by
    obtain ⟨_,hN,hE,_⟩ := c.linear_central_core_structure h hB hSyl hb hactor hcentral
      ht hne hcomm hnot eβ
    have hf : frattini (Q F v) ≤ (D F m t).subgroupOf (Q F v) :=
      @frattini_le_of_elementary_quotient (Q F v) _ _ 2 _
        (isPGroup_pCoreIn 2 (stabilizer F v)) ((D F m t).subgroupOf (Q F v)) hN hE
    have hh := map_mono (f := (Q F v).subtype) hf
    have hZQ : Z F v ≤ Q F v := fun _ hx =>
      ((mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h v).1 hx)).1
    rwa [map_subgroupOf_eq_of_le (hD.symm ▸ hZQ),hD] at hh
  have hJ : J ≠ ⊥ := by
    intro hh
    have hPhi : frattini (Q F v) = ⊥ :=
      ((frattini (Q F v)).map_eq_bot_iff_of_injective (Q F v).subtype_injective).mp hh
    exact c.exceptional_linear_core_not_elementary h hB hSyl hb hactor hcentral ht hne
      hcomm hnot eβ hD E ((frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hPhi)
  have hn : c.actor ≤ normalizer (J : Set G) := by
    apply le_normalizer_iff.mpr
    intro a ha x hx
    obtain ⟨y,hy,rfl⟩ := hx
    let φ := c.coreConjugation ⟨a,ha⟩
    have hφ : φ y ∈ frattini (Q F v) :=
      characteristic_iff_le_comap.mp inferInstance φ hy
    exact ⟨φ y,hφ,rfl⟩
  let : c.representation.IsIrreducible := center_representation_irreducible c E
  let : IsIrreducible (c.representation.comp c.quotient) :=
    (irreducible_comp_surjective_iff c.quotient c.onto c.representation).mpr inferInstance
  exact (c.coordinates.eq_kernel_or_section J (hω ▸ bot_le) hJZ hn).resolve_left
    (fun hh => hJ (hh.trans hω))

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
