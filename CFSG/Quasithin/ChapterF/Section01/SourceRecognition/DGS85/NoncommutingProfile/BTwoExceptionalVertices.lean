module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalCoreRecognition
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SecondRecognition
public import Theory.GroupTheory.WreathedThirtyTwoVertex.Recognition

/-!
# Binary exceptional local vertices

The homocyclic alpha core and its self-centralizing order-96 enlargement
identify that enlargement with the actual abelian-core parabolic of G₂(2)′.
Sylow conjugacy then identifies the unchanged adjacent-core product with
C₄ wreath C₂. The beta commutator identity proves its core nonabelian;
the wreathed centric-core recognition gives Q₈ ◦ C₄ and identifies the
beta enlargement with the other actual G₂(2)′ parabolic.

The adjacent-core product is also identified with the full edge two-core,
so the companion source application retains the original full Borel core.
These are local enlargement equivalences. Restoring the full endpoints
and full Borel, and proving the path parameters, remain source obligations.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985), proof
of (10.9), printed p.163. The native octonion models and their attribution
are supplied by the existing ATLAS imports; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local instance binaryVertexAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

private theorem local_core_selfCentralizing (h : LocallyRankOneTriple P B) (m : Vertex F) :
    centralizer (pCore 2 (graphLocalGroup F m) : Set (graphLocalGroup F m)) ≤
      pCore 2 (graphLocalGroup F m) := by
  let := finite_endpoints h
  let A := graphLocalGroup F m
  let H := stabilizer F m
  have hAH : A ≤ H := sylowGenerated_le _
  let : Finite A := Finite.of_injective (inclusion hAH) (inclusion_injective _)
  let N := A.subgroupOf H
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hAH).mpr (sylowGenerated_normalized H)
  have hh := normal_core_selfCentralizing (source_vertex_core_selfCentralizing h m) N
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (subgroupOfEquivOfLe hAH)).mp hh

/-- The actual alpha enlargement is the native abelian-core G₂(2)′ parabolic. -/
theorem BTwoCenterActionData.exceptional_binary_alpha_vertex
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
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (hK : Nat.card K = 2) :
    Nonempty (c.actor ≃* Atlas.G2.BinaryParabolicPair.derivedSecond) := by
  let := finite_endpoints h
  let : Finite c.actor := Finite.of_injective (inclusion c.actor_le) (inclusion_injective _)
  obtain ⟨eQ⟩ := c.exceptional_binary_alpha_core_equiv h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ hD E hK
  let eker := ((MulEquiv.subgroupCongr c.kernel).trans
    (subgroupOfEquivOfLe c.core_le)).trans eQ
  have hk := c.exceptional_linear_alpha_field_binary h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ hD E
  have hcard := (c.exceptional_binary_alpha_complement h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ hD E hK).1
  have hker : c.quotient.ker = pCore 2 c.actor := by
    apply map_injective c.actor.subtype_injective
    rw [c.kernel,map_subgroupOf_eq_of_le c.core_le]
    exact (show c.actor.pCoreIn 2 = Q F v from hactor ▸ sylowGenerated_core _).symm
  have hself : centralizer (c.quotient.ker : Set c.actor) ≤ c.quotient.ker := by
    rw [hker]
    exact hactor ▸ local_core_selfCentralizing h v
  let ep := MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
    ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  obtain ⟨es⟩ := BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two hk
  exact Atlas.G2.BinaryParabolicPair.equiv_derivedSecond_of_c4_square
    c.quotient.ker eker hcard hself
    ((QuotientGroup.quotientKerEquivOfSurjective c.quotient c.onto).trans (ep.trans es))

private theorem sylow_wreathed_of_alpha_equiv {H : Type*} [Group H] [Finite H]
    (R : Sylow 2 H) (e : H ≃* Atlas.G2.BinaryParabolicPair.derivedSecond) :
    Nonempty (R ≃* Theory.GroupTheory.WreathedThirtyTwo) := by
  let T := R.mapSurjective (f := e.toMonoidHom) e.surjective
  let er : R ≃* T := (R : Subgroup H).equivMapOfInjective e.toMonoidHom e.injective
  let es := T.equiv Atlas.G2.BinaryParabolicPair.derivedSecondSylow
  let et := subgroupOfEquivOfLe Atlas.G2.BinaryParabolicPair.derivedSylow_le_second
  obtain ⟨ew⟩ := Atlas.G2.BinaryParabolicPair.derivedSylow_isWreathedOfHeight.nonempty_mulEquiv_regularWreath
  exact ⟨er.trans (es.trans (et.trans ew))⟩

/-- The literal common core product is C₄ wreath C₂. -/
theorem BTwoCenterActionData.exceptional_binary_core_product_wreathed
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
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (hK : Nat.card K = 2) :
    Nonempty ((Q F m ⊔ Q F v : Subgroup G) ≃* Theory.GroupTheory.WreathedThirtyTwo) := by
  let := finite_endpoints h
  let : Finite c.actor := Finite.of_injective (inclusion c.actor_le) (inclusion_injective _)
  obtain ⟨e⟩ := c.exceptional_binary_alpha_vertex h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ hD E hK
  obtain ⟨T,hT⟩ := c.core_product_sylow h
  obtain ⟨R,hR⟩ := T.exists_map_subtype_eq_of_le c.actor_le
    (hT ▸ sup_le c.neighbor_core_le c.core_le)
  obtain ⟨ew⟩ := sylow_wreathed_of_alpha_equiv R e
  let er := ((R : Subgroup c.actor).equivMapOfInjective c.actor.subtype
    c.actor.subtype_injective).trans (MulEquiv.subgroupCongr (hR.trans hT))
  exact ⟨er.symm.trans ew⟩

private theorem edge_core_local_sylow
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b : Vertex F} (hab : (graph F).Adj a b) :
    ∃ R : Sylow 2 (graphLocalGroup F a),
      (R : Subgroup (graphLocalGroup F a)).map (graphLocalGroup F a).subtype =
        (stabilizer F a ⊓ stabilizer F b).pCoreIn 2 := by
  let := finite_endpoints h
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hSyl hab
  have he := sylow_image_eq_edge_core (stabilizer F a)
    (stabilizer F a ⊓ stabilizer F b) inf_le_left (source_edge_core_sylow h hB hab) T hT
  obtain ⟨R,hR⟩ := T.exists_map_subtype_eq_of_le (sylowGenerated_le _)
    (sylow_le_sylowGenerated _ T)
  exact ⟨R,hR.trans he⟩

/-- The core product is the entire two-core of the edge stabilizer. -/
theorem BTwoCenterActionData.core_product_eq_edge_core
    (h : LocallyRankOneTriple P B) {v m w : Vertex F}
    (c : BTwoCenterActionData F v m w k W) :
    Q F m ⊔ Q F v = (stabilizer F m ⊓ stabilizer F v).pCoreIn 2 := by
  have hQv : Q F v ≤ (stabilizer F m ⊓ stabilizer F v).pCoreIn 2 := by
    simpa only [inf_comm] using graph_Q_le_edgeCore h c.middle
  have hQm := graph_Q_le_edgeCore h c.middle.symm
  obtain ⟨T,hT⟩ := c.core_product_sylow h
  have he := inf_eq_sylow_map T (isPGroup_pCoreIn 2 (stabilizer F m ⊓ stabilizer F v))
    (hT ▸ sup_le hQm hQv)
  rw [inf_of_le_left ((pCoreIn_le 2 _).trans inf_le_right),hT] at he
  exact he.symm

/-- Recognize the unchanged beta core and its actual Chapter 6 enlargement. -/
theorem BTwoCenterActionData.exceptional_binary_beta_vertex
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ = Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K))
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (hK : Nat.card K = 2) :
    Nonempty (Q F m ≃* QuaternionCyclic.Model) ∧
      Nonempty (graphLocalGroup F m ≃* Atlas.G2.BinaryParabolicPair.derivedFirst) := by
  let := finite_endpoints h
  let A := graphLocalGroup F m
  let : Finite A := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (Q F m) := Finite.of_injective (inclusion (Q_le_stabilizer F m))
    (inclusion_injective _)
  have hc : A.pCoreIn 2 = Q F m := sylowGenerated_core _
  let eQ : pCore 2 A ≃* Q F m :=
    ((pCore 2 A).equivMapOfInjective A.subtype A.subtype_injective).trans
      (MulEquiv.subgroupCongr hc)
  have hk := c.exceptional_linear_alpha_field_binary h hB hSyl hb hactor hcentral
    ht hne hcomm.le hnot eβ hD E
  have hQcard : Nat.card (Q F m) = 16 := by
    have hh := (c.exceptional_linear_core_orders h hB hSyl hb hactor hcentral
      ht hne hcomm.le hnot eβ hD E).2
    simpa [hk,hK] using hh
  have hcard : Nat.card A = 96 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (pCore 2 A)
    rw [Nat.card_congr eβ.toEquiv,BenderSuzuki.External.huppert614_card_specialLinearGroup,
      hK,Nat.card_congr eQ.toEquiv,hQcard] at hh
    norm_num at hh
    exact hh
  have hnon : ¬ IsMulCommutative (Q F m) := by
    intro hm
    have hbot : ⁅Q F m,Q F m⁆ = ⊥ := by
      have hh := congrArg (map (Q F m).subtype) ((commutator_eq_bot_iff (Q F m)).mpr hm)
      simpa only [_root_.commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype,Subgroup.map_bot] using hh
    have hzbot : Z F m = ⊥ := (c.beta_core_frattini_eq h hB hSyl hb hactor hcentral
      ht hne hcomm).2.symm.trans hbot
    have hz := c.central_middle_center_card h hB hSyl hb hactor hcentral E
    rw [hzbot,card_bot,hk] at hz
    omega
  have hn : ¬ IsMulCommutative (pCore 2 A) := by
    intro hm
    exact hnon (IsMulCommutative.of_comm (fun x y => eQ.symm.injective (by
      rw [map_mul,map_mul]; exact hm.is_comm.comm _ _)))
  have hcover := (c.core_product_eq_edge_core h).symm
  obtain ⟨R,hR⟩ := edge_core_local_sylow h hB hSyl c.middle.symm
  rw [hcover] at hR
  let er : R ≃* (Q F m ⊔ Q F v : Subgroup G) :=
    ((R : Subgroup A).equivMapOfInjective A.subtype A.subtype_injective).trans
      (MulEquiv.subgroupCongr hR)
  obtain ⟨ew⟩ := c.exceptional_binary_core_product_wreathed h hB hSyl hb hactor hcentral
    ht hne hcomm.le hnot eβ hD E hK
  obtain ⟨em⟩ := WreathedVertex.twoCore_equiv_of_card96 hcard
    (local_core_selfCentralizing h m) hn R (er.trans ew)
  exact ⟨⟨eQ.symm.trans em⟩,WreathedVertex.equiv_derivedFirst_of_card96 hcard
    (local_core_selfCentralizing h m) hn R (er.trans ew)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
