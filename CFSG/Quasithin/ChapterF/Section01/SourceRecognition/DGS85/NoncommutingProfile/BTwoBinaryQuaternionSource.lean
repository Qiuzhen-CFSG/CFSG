module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBinaryQuaternion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoIntrinsicCoreOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearValence

/-!
# The original binary quaternion clause of Chapter 10

The original binary beta quotient forces the constructed alpha field to
have order two and computes the beta valence as three. The radius-group
recognition then identifies the actual V_beta with Q₈ ◦ C₄ and its
commutator with the actual beta enlargement with Q₈. The original core
product, Frattini subgroup and derived subgroup are retained with their
literal inclusions. Both exceptional and strict binary cases are covered;
no nonsolvability or terminal-core separation is imposed.

Source: DGS, Groups and Graphs (1985), (10.7)(c), pp.158--159,
(10.8), pp.161--162, and (10.10)(d), p.164. The nonbinary irreducibility
clause and strict path parameters are separate remaining obligations.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local notation "ι" => Subgroup.subtype (G₀ L S)

/-- The literal original binary beta radius group and its quaternion commutator.
The natural action and the alpha field size are constructed from the original
source. Both exceptional and strict rows are retained. -/
theorem original_bTwo_binary_radius_quaternion
    (h : HypothesisF11 L S) {u t : Vertex F₀}
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆≠⊥)
    (hb : b F₀=2) (hβu : (graph F₀).Adj β u)
    (ht : (graph F₀).Adj α t) (htne : t≠β)
    (e : (L 1 ⧸ pCore 2 (L 1))≃*PSL(2,K)) (hK : Nat.card K=2) :
    let V₁ := (V F₀ β 1).map ι
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let D₀ := Q₁⊓(Q F₀ t).map ι
    let Z₁ := (Z F₀ β).map ι
    Nat.card V₁=16 ∧ Nonempty (V₁≃*QuaternionCyclic.Model) ∧
      Nonempty ((⁅V₁,enlargedEndpoint L S 1⁆ : Subgroup G)≃*QuaternionGroup 2) ∧
      V₁≤Q₁ ∧ Q₁=V₁⊔D₀ ∧
      (frattini Q₁).map Q₁.subtype=Z₁ ∧ ⁅Q₁,Q₁⁆=Z₁ := by
  have hab : (graph F₀).Adj α β :=
    ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ :=
    reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have halg : alg=ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2
  have hnot := reduced_graph_core_obstruction h α β hab
  let H := reduced_triple h
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have hk : Nat.card k=2 := by
    have hh := (c.linear_central_core_structure H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm.le hnot eβ).1
    have hmin : 1<Nat.card k := Finite.one_lt_card
    rw [hK] at hh
    omega
  have hval : Nat.card ((graph F₀).neighborSet β)=3 := by
    have hi := source_linear_edge_index_of_quotient H (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) hab.symm eβ
    rw [card_neighbor_base]
    change (F₀ false).relIndex (F₀ true)=3
    change (stabilizer F₀ α).relIndex (stabilizer F₀ β)=Nat.card K+1 at hi
    simpa only [Subgroup.CosetGeometry.stabilizer_base,hK] using hi
  obtain ⟨hcard,⟨eV⟩,⟨eM⟩⟩ := c.binary_radius_structure H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb hactor hcentral (LinearEquiv.refl _ _) hk hcomm hne hval
  have hlayers := original_bTwo_beta_core_frattini h hb c hactor hcentral ht htne hcomm
  have hVQ := graph_V_le_Q_of_short H (reduced_kernel_sylow h) β (i:=1) (by change 1<b F₀; rw [hb]; decide)
  have hmap : (⁅V F₀ β 1,graphLocalGroup F₀ β⁆).map ι =
      ⁅(V F₀ β 1).map ι,enlargedEndpoint L S 1⁆ := by
    rw [map_commutator,reduced_graphLocalGroup_image h true]
    rfl
  refine ⟨(card_map_of_injective (G₀ L S).subtype_injective).trans hcard,
    ⟨((V F₀ β 1).equivMapOfInjective ι (G₀ L S).subtype_injective).symm.trans eV⟩,
    ⟨(MulEquiv.subgroupCongr hmap.symm).trans
      (((⁅V F₀ β 1,graphLocalGroup F₀ β⁆).equivMapOfInjective ι
        (G₀ L S).subtype_injective).symm.trans eM)⟩,?_,
    original_bTwo_beta_core_product h hb c ht htne,hlayers⟩
  have hh := map_mono (f:=ι) hVQ
  change (V F₀ β 1).map ι≤(Q F₀ β).map ι at hh
  rwa [reduced_base_Q_map h true] at hh

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
