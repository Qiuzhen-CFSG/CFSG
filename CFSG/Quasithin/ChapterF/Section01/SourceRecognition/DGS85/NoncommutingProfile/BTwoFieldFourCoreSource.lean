module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalFieldBoundSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalCubicSource

/-!
# Original-endpoint application of the field-four core recognition

The preceding helper is now applied to the literal original beta core.  The
quotient order and full core order are transported from the original endpoint
maps, and the order-five Frattini actor and rank bound remain named source
premises.  This is exactly the point at which the DGS proof begins its J₂
recognition; no parabolic equivalence or path parameter is hidden in the
consumer.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance fieldFourSourceAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] :
    Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2

theorem original_bTwo_field_four_beta_minus_model
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
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hk : Nat.card k = 2)
    (hK : Nat.card K = 4)
    (a : MulAut ((parabolic L S 1).pCoreIn 2))
    (ha : orderOf (quotientAut (frattini ((parabolic L S 1).pCoreIn 2)) a) = 5)
    (hrank : ∀ E : Subgroup ((parabolic L S 1).pCoreIn 2),
      IsElementaryAbelian 2 E → Nat.card E < 8)
    (hnon : ¬ IsMulCommutative ((parabolic L S 1).pCoreIn 2)) :
    Nonempty ((parabolic L S 1).pCoreIn 2 ≃* MinusExtraspecial.Model) := by
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let _ : Finite (parabolic L S 1) := h.finite_parabolic 1
  let _ : Finite Q₁ := Finite.of_injective
    (inclusion (show Q₁ ≤ parabolic L S 1 from pCoreIn_le 2 _)) (inclusion_injective _)
  have hparam := (original_bTwo_exceptional_beta_parameters h hb c hactor hcentral
    ht hne hcomm hnot e hD E).1
  have hquot : Nat.card (Q₁ ⧸ frattini Q₁) = 16 := by
    simpa [Q₁, hk, hK] using hparam
  have horders := original_bTwo_exceptional_linear_core_orders h hb c hactor hcentral
    ht hne hcomm.le hnot e (by
      apply map_injective (G₀ L S).subtype_injective
      change (Q F₀ β ⊓ Q F₀ t).map (G₀ L S).subtype = _
      rw [map_inf _ _ _ (G₀ L S).subtype_injective, reduced_base_Q_map h true]
      exact hD) E
  have hcard : Nat.card Q₁ = 32 := by
    simpa [Q₁, hk, hK] using horders.2
  have hphi : Nat.card (frattini Q₁) = 2 := by
    have hh := (frattini Q₁).index_mul_card
    change Nat.card (Q₁ ⧸ frattini Q₁) * Nat.card (frattini Q₁) = Nat.card Q₁ at hh
    rw [hquot, hcard] at hh
    omega
  let hQ : IsPGroup 2 Q₁ := isPGroup_pCoreIn 2 (parabolic L S 1)
  exact field_four_beta_minus_model hQ hnon hphi hquot a ha hrank

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
