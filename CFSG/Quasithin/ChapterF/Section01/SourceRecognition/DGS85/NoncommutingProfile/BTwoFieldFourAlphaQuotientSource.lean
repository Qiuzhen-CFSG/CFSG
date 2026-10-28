module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourAlphaCoreSource
public import Theory.GroupTheory.NormalSymmetricThreeCubic
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# The full field-four alpha quotient with its original marking

The actual enlarged alpha subgroup is normal in the full reduced endpoint.
Its quotient is SL₂(2), hence S₃. The full quotient has order eighteen, so
the completeness of S₃ splits off its cubic centralizer. The product map
preserves the original center-action quotient on every actor representative.
It also supplies a nontrivial central cubic coset in the actual alpha endpoint.

Restoring the common original extension index gives both endpoint orders,
the full Borel and Sylow orders, and the alpha quotient order. No parabolic
equivalence or endpoint splitting is assumed here. Recognition of the full
alpha endpoint with the compatible Borel map remains the next step.

Source: Delgado–Goldschmidt–Stellmacher, *Groups and Graphs* (1985),
(10.9), printed pp.162–163, and the reduction on pp.95–96.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
open Theory.GroupTheory
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance fieldFourAlphaQuotientAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2


local notation "S3" => Equiv.Perm (Fin 3)
local notation "C3" => Multiplicative (ZMod 3)

private theorem original_alpha_actor_quotient
    (h : HypothesisF11 L S) {u : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α) :
    ∃ j : c.actor ≃* enlargedEndpoint L S 0,
      (∀ a : c.actor, (j a : G) = ((a : G₀ L S) : G)) ∧
      ∃ d : (enlargedEndpoint L S 0 ⧸ pCore 2 (enlargedEndpoint L S 0)) ≃* SL(2,k),
        ∀ a : c.actor, d (QuotientGroup.mk' (pCore 2 (enlargedEndpoint L S 0)) (j a)) =
          c.quotient a := by
  let : ∀ i, Finite (F₀ i) := finite_endpoints (reduced_triple h)
  have hc : pCore 2 c.actor = (Q F₀ α).subgroupOf c.actor := by
    apply map_injective c.actor.subtype_injective
    rw [map_subgroupOf_eq_of_le c.core_le]
    change c.actor.pCoreIn 2 = _
    rw [hactor]
    exact sylowGenerated_core (stabilizer F₀ α)
  have ha : c.actor.map (G₀ L S).subtype = enlargedEndpoint L S 0 := by
    rw [hactor,reduced_graphLocalGroup_image h false]
    rfl
  let j : c.actor ≃* enlargedEndpoint L S 0 :=
    (c.actor.equivMapOfInjective (G₀ L S).subtype (G₀ L S).subtype_injective).trans
      (MulEquiv.subgroupCongr ha)
  let d₀ : (c.actor ⧸ pCore 2 c.actor) ≃* SL(2,k) :=
    (QuotientGroup.quotientMulEquivOfEq (hc.trans c.kernel.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective c.quotient c.onto)
  let qj := QuotientGroup.congr (pCore 2 c.actor) (pCore 2 (enlargedEndpoint L S 0))
    j (pCore_map_iso 2 j)
  refine ⟨j,fun _ => rfl,qj.symm.trans d₀,fun a => ?_⟩
  change d₀ (qj.symm (qj (QuotientGroup.mk' (pCore 2 c.actor) a))) = _
  rw [qj.symm_apply_apply]
  rfl

/-- The entire reduced alpha quotient is S₃ × C₃, with the original alpha
actor mapping to the first factor on every literal representative. -/
theorem original_bTwo_field_four_reduced_alpha_quotient
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    ∃ j : c.actor ≃* enlargedEndpoint L S 0,
      (∀ a : c.actor, (j a : G) = ((a : G₀ L S) : G)) ∧
      ∃ (eK : SL(2,k) ≃* S3)
        (d : (P₀ L S 0 ⧸ pCore 2 (P₀ L S 0)) ≃* S3 × C3),
        ∀ a : c.actor,
          d (QuotientGroup.mk' (pCore 2 (P₀ L S 0))
            (inclusion (show enlargedEndpoint L S 0 ≤ P₀ L S 0 from
              sup_le le_sup_left (le_sup_right.trans le_sup_right)) (j a))) =
            (eK (c.quotient a),1) := by
  let P := P₀ L S 0
  let X := enlargedEndpoint L S 0
  have hXP : X ≤ P := sup_le le_sup_left (le_sup_right.trans le_sup_right)
  let : Finite (parabolic L S 0) := h.finite_parabolic 0
  let : Finite P := Finite.of_injective (inclusion (P₀_le h 0)) (inclusion_injective _)
  let I := X.subgroupOf P
  let : I.Normal := (normal_subgroupOf_iff_le_normalizer hXP).mpr (by
    change P₀ L S 0 ≤ normalizer (enlargedEndpoint L S 0 : Set G)
    rw [←reduced_sylowGenerated_eq h 0]
    exact sylowGenerated_normalized (P₀ L S 0))
  obtain ⟨j,hj,eX,heX⟩ := original_alpha_actor_quotient h c hactor
  have hk := (original_bTwo_exceptional_fields_and_orders
    h hb c hactor hcentral ht hne hcomm hnot e hD E).1
  let : Fintype k := Fintype.ofFinite k
  let aK : k ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card,ZMod.card] using hk)
  let eK := (Atlas.fieldEquivSL 2 aK).trans SLTwoPermThree.sl2Two_equiv_perm_three.some
  let aI : I ≃* X := subgroupOfEquivOfLe hXP
  let eI := (QuotientGroup.congr (pCore 2 I) (pCore 2 X) aI (pCore_map_iso 2 aI)).trans
    (eX.trans eK)
  have hc := (original_bTwo_field_four_reduced_alpha_orders
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK).2.2
  obtain ⟨d,hd⟩ := Theory.GroupTheory.NormalSymmetricThreeFactor.exists_marked_core_cubic_product I eI hc
  refine ⟨j,hj,eK,d,fun a => ?_⟩
  have hh := hd (aI.symm (j a))
  change d (QuotientGroup.mk' (pCore 2 P) (inclusion hXP (j a))) =
    (eK (eX (QuotientGroup.mk' (pCore 2 X) (j a))),1) at hh
  rw [heX] at hh
  exact hh

/-- The common original extension index determines both full endpoint orders,
including the alpha quotient order. -/
theorem original_bTwo_field_four_full_pair_orders
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    ∃ n : ℕ, (n = 1 ∨ n = 2) ∧
      (B₀ L S).relIndex (commonBorel L S) = n ∧
      (∀ i : Fin 2, (P₀ L S i).relIndex (parabolic L S i) = n) ∧
      Nat.card (parabolic L S 0) = 1152 * n ∧
      Nat.card (parabolic L S 1) = 1920 * n ∧
      Nat.card (commonBorel L S) = 384 * n ∧ Nat.card S = 128 * n ∧
      Nat.card (parabolic L S 0 ⧸ pCore 2 (parabolic L S 0)) = 18 * n := by
  obtain ⟨_,_,_,_,_,n,hn,hB,hpi,hβ,hBor,hS⟩ :=
    original_bTwo_field_four_original_extension
      h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  obtain ⟨_,hα,_⟩ := original_bTwo_field_four_reduced_alpha_orders
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  have hp := relIndex_mul_relIndex (⊥ : Subgroup G) (P₀ L S 0)
    (parabolic L S 0) bot_le (P₀_le h 0)
  rw [relIndex_bot_left,relIndex_bot_left,hα,hpi] at hp
  have hQ := (original_bTwo_field_four_structure
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK).1
  have hcore : Nat.card (pCore 2 (parabolic L S 0)) = 64 := by
    rw [←card_map_of_injective (parabolic L S 0).subtype_injective]
    exact hQ
  have hquot := (pCore 2 (parabolic L S 0)).card_mul_index
  rw [hcore,←hp,index_eq_card] at hquot
  refine ⟨n,hn,hB,hpi,hp.symm,hβ,hBor,hS,?_⟩
  omega

/-- The central cubic factor gives an actual alpha element with nontrivial
central coset modulo the original reduced two-core. -/
theorem original_bTwo_field_four_alpha_central_cubic
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    ∃ a : P₀ L S 0, a ∉ pCore 2 (P₀ L S 0) ∧
      a ^ 3 ∈ pCore 2 (P₀ L S 0) ∧
      ∀ x : P₀ L S 0, ⁅a,x⁆ ∈ pCore 2 (P₀ L S 0) := by
  obtain ⟨j,hj,eK,d,hd⟩ := original_bTwo_field_four_reduced_alpha_quotient
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  exact NormalSymmetricThreeFactor.exists_central_cubic_coset _ d

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
