module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalCubic
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.OriginalBTwoEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBetaCoreSource

/-!
# Intrinsic core orders before the exceptional/strict split

The saturated alpha quotient has order q_beta squared. The adjacent-core
intersection has index q_beta over D_alpha, and index q_alpha in Q_beta.
These give both core orders without imposing D_alpha = Z_alpha or
nonsolvability. Since Z_alpha is contained in D_alpha and has order
q_alpha squared, equality in the beta-core lower bound is equivalent to
the exceptional condition. Strict inequality retains the binary strict case.

The original-source application constructs its natural action internally
and uses the literal beta quotient marking. It retains the full original
core maps and the Frattini and derived subgroup of the beta core.

Source: DGS, Groups and Graphs (1985), (10.4), (10.7), and the split in
(10.9)--(10.10), printed pp.155--165.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

/-- Both core orders over the actual D subgroup, before selecting a branch. -/
theorem BTwoCenterActionData.linear_core_orders_over_D
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
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K)) :
    Nat.card (Q F v) = Nat.card K ^ 2 * Nat.card (D F m t) ∧
      Nat.card (Q F m) = Nat.card k * Nat.card K * Nat.card (D F m t) := by
  let := finite_endpoints h
  have hS := source_kernel_sylow h hB hSyl
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,_,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  obtain ⟨_,hN,hE,hcard⟩ := c.linear_central_core_structure h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ
  let := hN
  have hQa := card_eq_card_quotient_mul_card_subgroup ((D F m t).subgroupOf (Q F v))
  rw [hcard,Nat.card_congr (subgroupOfEquivOfLe d.separated).toEquiv] at hQa
  refine ⟨hQa,?_⟩
  let I := Q F v ⊓ Q F m
  have hDI : D F m t ≤ I := le_inf d.separated inf_le_left
  have hI := ((D F m t).subgroupOf I).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hDI).toEquiv] at hI
  change (D F m t).relIndex I * Nat.card (D F m t) = Nat.card I at hI
  rw [c.linear_seed_factor_index h hB hSyl hS hb ht hne hnot eβ] at hI
  have hi := relIndex_ker (K := (Q F m).subgroupOf c.actor) c.quotient
  rw [c.kernel,relIndex_subgroupOf c.neighbor_core_le,c.neighbor_image] at hi
  have hindex : (Q F v).relIndex (Q F m) = Nat.card k := hi.trans
    (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 c.imageSylow).symm.toEquiv)
  have hQb := (I.subgroupOf (Q F m)).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (show I ≤ Q F m from inf_le_right)).toEquiv] at hQb
  change I.relIndex (Q F m) * Nat.card I = Nat.card (Q F m) at hQb
  have hi' : I.relIndex (Q F m) = Nat.card k := by
    dsimp only [I]
    rw [inf_comm,inf_relIndex_left]
    exact hindex
  rw [hi',←hI] at hQb
  rw [←hQb]
  ring

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile

namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local notation "ι" => Subgroup.subtype (G₀ L S)

/-- The original cores, their exact orders over D, and the numerical test
for the exceptional branch. No nonsolvability or natural-action input is used. -/
theorem original_bTwo_intrinsic_core_orders
    (h : HypothesisF11 L S) {u t : Vertex F₀}
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆ ≠ ⊥)
    (hb : b F₀ = 2) (hβu : (graph F₀).Adj β u)
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) :
    ∃ (k : Type u) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
      (_ : Algebra (ZMod 2) k),
      ∃ c : BTwoCenterActionData F₀ α β u k (Fin 2 → k),
      c.actor = graphLocalGroup F₀ α ∧
      let Q₀ := (parabolic L S 0).pCoreIn 2
      let Q₁ := (parabolic L S 1).pCoreIn 2
      let D₀ := Q₁ ⊓ (Q F₀ t).map ι
      let Z₀ := (Z F₀ α).map ι
      let Z₁ := (Z F₀ β).map ι
      Z₀ ≤ D₀ ∧ D₀ ≤ Q₀ ∧ IsElementaryAbelian 2 D₀ ∧
      Nat.card Z₀ = Nat.card k ^ 2 ∧
      Nat.card Q₀ = Nat.card K ^ 2 * Nat.card D₀ ∧
      Nat.card Q₁ = Nat.card k * Nat.card K * Nat.card D₀ ∧
      Nat.card k ^ 3 * Nat.card K ≤ Nat.card Q₁ ∧
      (D₀ = Z₀ ↔ Nat.card Q₁ = Nat.card k ^ 3 * Nat.card K) ∧
      (D₀ ≠ Z₀ ↔ Nat.card k ^ 3 * Nat.card K < Nat.card Q₁) ∧
      (frattini Q₁).map Q₁.subtype = Z₁ ∧ ⁅Q₁,Q₁⁆ = Z₁ ∧
      Nat.card k ≤ Nat.card K ∧
      P₀ L S 0 ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) ∧
      B₀ L S ≤ normalizer (Q₀ : Set G) ⊓ normalizer (D₀ : Set G) := by
  have hab : (graph F₀).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ :=
    reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have halg : alg = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2
  have hnot := reduced_graph_core_obstruction h α β hab
  let H := reduced_triple h
  let eβ := (reduced_graphLinearQuotient h true e).trans
    (MulEquiv.ofBijective (BenderSuzuki.Converse.pi K)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  have horders := c.linear_core_orders_over_D H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hb hactor hcentral ht htne hcomm.le hnot eβ
  have hω := c.omega_eq_bot_of_central_neighbor H (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hactor hcentral
  have hZcard := c.central_center_card (LinearEquiv.refl _ _) hω
  obtain ⟨g,hg,hDQ,hnorm,hDel,hdec,hdis⟩ :=
    original_bTwo_central_D_structure h hb c hactor hcentral ht htne
  have hlayers := original_bTwo_linear_core_layers h hb c hactor hcentral
    ht htne hcomm hnot e
  have hnorms := original_bTwo_seed_layers_normalized h hb c ht htne
  have hsat := (original_bTwo_linear_seed_and_indices h hb c ht htne hnot e).1
  dsimp only at hnorms
  rw [hsat] at hnorms
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let D₀ := Q₁ ⊓ (Q F₀ t).map ι
  let Z₀ := (Z F₀ α).map ι
  have hDm : (D F₀ β t).map ι = D₀ := by
    change (Q F₀ β ⊓ Q F₀ t).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    rfl
  have hQam : (Q F₀ α).map ι = Q₀ := reduced_base_Q_map h false
  have hQbm : (Q F₀ β).map ι = Q₁ := reduced_base_Q_map h true
  have hQa : Nat.card Q₀ = Nat.card K ^ 2 * Nat.card D₀ := by
    rw [←hQam,←hDm,
      card_map_of_injective (G₀ L S).subtype_injective,
      card_map_of_injective (G₀ L S).subtype_injective]
    exact horders.1
  have hQb : Nat.card Q₁ = Nat.card k * Nat.card K * Nat.card D₀ := by
    rw [←hQbm,←hDm,
      card_map_of_injective (G₀ L S).subtype_injective,
      card_map_of_injective (G₀ L S).subtype_injective]
    exact horders.2
  have hZ : Nat.card Z₀ = Nat.card k ^ 2 :=
    (card_map_of_injective (G₀ L S).subtype_injective).trans hZcard
  have hZD : Z₀ ≤ D₀ := by
    change (Z F₀ α).map ι ≤ (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map ι
    rw [hdec]
    exact le_sup_left
  let := h.finite_parabolic 0
  let : Finite Q₀ := Finite.of_injective (inclusion (pCoreIn_le 2 _)) (inclusion_injective _)
  let : Finite D₀ := Finite.of_injective (inclusion hDQ) (inclusion_injective _)
  have hle : Nat.card k ^ 2 ≤ Nat.card D₀ := hZ ▸ card_le_of_le hZD
  have hlower : Nat.card k ^ 3 * Nat.card K ≤ Nat.card Q₁ := by
    rw [hQb]
    calc
      Nat.card k ^ 3 * Nat.card K = Nat.card k * Nat.card K * Nat.card k ^ 2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hle
  have hiff : D₀ = Z₀ ↔ Nat.card Q₁ = Nat.card k ^ 3 * Nat.card K := by
    constructor
    · intro he
      rw [hQb,he,hZ]
      ring
    · intro he
      apply (eq_of_le_of_card_ge hZD ?_).symm
      have hcount : Nat.card k * Nat.card K * Nat.card D₀ =
          Nat.card k * Nat.card K * Nat.card k ^ 2 := by
        rw [←hQb,he]
        ring
      have hpos : 0 < Nat.card k * Nat.card K := Nat.mul_pos Nat.card_pos Nat.card_pos
      rw [Nat.mul_left_cancel hpos hcount,hZ]
  refine ⟨k,f,fin,ch,inferInstance,c,hactor,hZD,hDQ,hDel,hZ,hQa,hQb,hlower,hiff,
    ?_,hlayers.2.1,hlayers.2.2.1,hlayers.2.2.2.1,hnorms.1,hnorms.2⟩
  change D₀ ≠ Z₀ ↔ Nat.card k ^ 3 * Nat.card K < Nat.card Q₁
  rw [ne_eq,hiff]
  omega

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
