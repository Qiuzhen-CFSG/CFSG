module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.MarkedCores
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneRegularSource

/-!
# Equal-linear DGS profiles: root orders and commuting opposite roots

The earlier marked b=1 actions prove elementary abelianness of both full
original parabolic cores. The original endpoint isomorphisms therefore
make both pairs of opposite roots commute inside the same quotient.

To count the actual simple roots, transport the DGS neighbor count across
the reduced triple. The reduction preserves the entire Borel index because
both Borels have the same intersection with the starred endpoint. The
marked Bruhat index then gives |U_i| = |k_0| for both endpoints.

These deductions use the same earlier actions as original_bOne_profile;
the actor identities and natural dimension remain genuine earlier-source
inputs. The commuting clause retains the section 2/5 local-kernel
containment. Source-local and full root-generated group identifications
are separate remaining steps; no model group is assigned from an order.

Source: DGS (1985), reduction pp.95--96 and (10.5), pp.156--157;
Fong--Seitz I (6A)(a), printed pp.37--38.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
open DGS85.NoncommutingProfile DGS85.Reduction Subgroup.CosetGeometry.RankTwo
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)

private theorem reduced_original_borel_index (h : HypothesisF11 L S) (i : Fin 2) :
    (B₀ L S).relIndex (P₀ L S i) =
      (commonBorel L S).relIndex (parabolic L S i) := by
  let := h.finite_commonBorel
  let : Finite (B₀ L S) := Finite.of_injective
    (inclusion (B₀_le h)) (inclusion_injective _)
  have hn : commonBorel L S ≤ normalizer (starredParabolic L S i : Set G) :=
    (commonBorel_le_parabolic i).trans
      ((normal_subgroupOf_iff_le_normalizer (starredParabolic_le i)).mp
        (h.starredParabolic_normal i))
  rw [P₀, ← h.starredParabolic_supplement i,
    relIndex_sup_of_normalizes _ _ ((B₀_le h).trans hn),
    relIndex_sup_of_normalizes _ _ hn,
    ← inf_relIndex_right (B₀ L S), B₀_inf_star h i, inf_relIndex_right]

private theorem reduced_neighbor_original_index (h : HypothesisF11 L S) (i : Bool) :
    Nat.card ((graph (reducedFamily L S)).neighborSet (base (reducedFamily L S) i)) =
      (commonBorel L S).relIndex (parabolic L S (if i then 1 else 0)) := by
  rw [← reduced_original_borel_index h]
  have ht := (reduced_triple h).intersection
  cases i
  · rw [card_neighbor_base]
    change ((P₀ L S 1).subgroupOf (G₀ L S)).relIndex
      ((P₀ L S 0).subgroupOf (G₀ L S)) = _
    rw [← inf_relIndex_right, inf_comm, ht]
    exact relIndex_subgroupOf (show P₀ L S 0 ≤ G₀ L S from le_sup_left)
  · rw [card_neighbor_base]
    change ((P₀ L S 0).subgroupOf (G₀ L S)).relIndex
      ((P₀ L S 1).subgroupOf (G₀ L S)) = _
    rw [← inf_relIndex_right, ht]
    exact relIndex_subgroupOf (show P₀ L S 1 ≤ G₀ L S from le_sup_right)

variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
variable (h : HypothesisF11 L S)
    (c₀ : BOneActionData (reducedFamily L S)
      (base (reducedFamily L S) false)
      (base (reducedFamily L S) true) k₀ W₀)
    (c₁ : BOneActionData (reducedFamily L S)
      (base (reducedFamily L S) true)
      (base (reducedFamily L S) false) k₁ W₁)

include e h c₀ c₁

/-- Both full transported parabolic cores are elementary by DGS (10.5). -/
theorem marked_bOne_core_elementary (i : Fin 2) :
    IsElementaryAbelian 2 ((Q.tits.standardParabolic {Q.simple i}).pCoreIn 2) := by
  obtain ⟨h₀,h₁⟩ := original_cores_elementary_of_actions h c₀ c₁
  apply marked_core_elementary Q e i
  fin_cases i
  · exact h₀
  · exact h₁

/-- DGS (10.5) gives the (6A)(a) commuting clause in both endpoint orientations. -/
theorem marked_bOne_root_commutator (split : SplitData Q.tits)
    (i j : Fin 2) (hij : i ≠ j)
    (hV : simpleRemainder Q split j ≤ localKernel Q j) :
    ⁅simpleRoot Q split i, rootAt Q split i (Q.simple j)⁆ = ⊥ := by
  let := marked_bOne_core_elementary Q e h c₀ c₁ j
  exact Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.root_commutator_eq_bot_of_abelian_core
    Q split i j hij hV inferInstance

variable (hactor₀ : c₀.actor =
      ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 0).subgroupOf (G₀ L S))
    (hactor₁ : c₁.actor =
      ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 1).subgroupOf (G₀ L S))
local instance {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
include hactor₀ hactor₁

/-- The original marked actions give both literal simple-root orders, including q = 2. -/
theorem marked_bOne_simpleRoot_card (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀))
    (split : SplitData Q.tits) (i : Fin 2) :
    Nat.card (simpleRoot Q split i) = Nat.card k₀ := by
  have hn₀ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (c₀.actor : Set (G₀ L S)) := by
    rw [hactor₀]
    exact reduced_borel_normalizes_source_actor h 0
  have hn₁ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (c₁.actor : Set (G₀ L S)) := by
    rw [hactor₁]
    exact reduced_borel_normalizes_source_actor h 1
  have hi (b : Bool) := neighbor_card_of_actions (reduced_triple h)
    c₀ c₁ hn₀ hn₁ E₀ (base (reducedFamily L S) b)
  have he (b : Bool) := (reduced_neighbor_original_index h b).symm.trans (hi b)
  have hr := marked_commonBorel_root_index Q e h split i
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
  · have hzero := he false
    change (commonBorel L S).relIndex (parabolic L S 0) = Nat.card k₀ + 1 at hzero
    rw [hzero] at hr
    omega
  · have hone := he true
    change (commonBorel L S).relIndex (parabolic L S 1) = Nat.card k₀ + 1 at hone
    rw [hone] at hr
    omega

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
