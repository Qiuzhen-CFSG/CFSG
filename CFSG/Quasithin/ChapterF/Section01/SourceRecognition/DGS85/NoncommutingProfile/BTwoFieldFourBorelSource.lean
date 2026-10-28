module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourLiftSource
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.BorelRecognition

/-!
# The original beta enlargement and its marked Borel

Align the constructed endpoint isomorphism by Sylow conjugacy. The original
Borel two-core has order 128, and its normalizing intersection with the beta
enlargement has order 384. The native full Sylow normalizer has this same
order, so the endpoint map restricts to actual Sylow and Borel equivalences.
Both inclusion squares retain the original ambient subgroups.

This Borel is the intersection of the enlargement with the original full
Borel. A comparison of both full original endpoints and the full Borel,
including any remaining extension, still requires the amalgam argument.
Source: DGS, Groups and Graphs (1985), the exercise following (10.9), p.163.
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
local instance fieldFourBorelLiftAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

open MinusExtraspecial.AlternatingAction
local notation "Jβ" => Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.l₁
local notation "eJ" => Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.coreModelEquiv
local notation "jJ" => Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.centralActionEquiv

local notation "JB" => Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap.B
local notation "JS" => Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.s

/-- The literal enlargement Borel and Sylow maps extend the same endpoint map. -/
theorem original_bTwo_field_four_beta_enlargement_borel_equiv
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
    let X := enlargedEndpoint L S 1
    let T := (commonBorel L S).pCoreIn 2
    let B := X ⊓ commonBorel L S
    ∃ (f : X ≃* Jβ) (fT : T ≃* JS) (fB : B ≃* JB),
      (T.subgroupOf X).map f.toMonoidHom = (JS).subgroupOf Jβ ∧
      (B.subgroupOf X).map f.toMonoidHom = (JB).subgroupOf Jβ ∧
      (∀ t : T, (fT t : Sporadic.LeechRelated.J2.Carrier) =
        (f (inclusion (show T ≤ X from le_sup_right) t) : Sporadic.LeechRelated.J2.Carrier)) ∧
      ∀ b : B, (fB b : Sporadic.LeechRelated.J2.Carrier) =
        (f (inclusion inf_le_left b) : Sporadic.LeechRelated.J2.Carrier) := by
  let X := enlargedEndpoint L S 1
  let T := (commonBorel L S).pCoreIn 2
  let B := X ⊓ commonBorel L S
  have hTX : T ≤ X := le_sup_right
  have hBX : B ≤ X := inf_le_left
  obtain ⟨_,hT,hB,eX,heX,eN,f₀,hfN,hfaction,j,hjf,hj,d,hdmark,hdlocal⟩ :=
    original_bTwo_field_four_beta_enlargement_equiv
      h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  let : Finite X := Finite.of_injective f₀ f₀.injective
  have hT₀ : Nat.card (T.subgroupOf X) = 128 :=
    (Nat.card_congr (subgroupOfEquivOfLe hTX).toEquiv).trans hT
  have hB₀ : Nat.card (B.subgroupOf X) = 384 :=
    (Nat.card_congr (subgroupOfEquivOfLe hBX).toEquiv).trans hB
  have hnorm : commonBorel L S ≤ normalizer (T : Set G) :=
    (commonBorel L S).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (commonBorel L S)))
  have hn : B.subgroupOf X ≤ normalizer (T.subgroupOf X : Set X) := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro t
    change (t : G) ∈ T ↔ (x : G) * (t : G) * (x : G)⁻¹ ∈ T
    exact mem_normalizer_iff.mp (hnorm hx.2) (t : G)
  obtain ⟨f,hfT,hfB,fT₀,fB₀,hfT₀,hfB₀⟩ :=
    Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.exists_borel_aligned_equiv
      f₀ (T.subgroupOf X) (B.subgroupOf X) hT₀ hB₀ hn
  let fT := (subgroupOfEquivOfLe hTX).symm.trans
    (fT₀.trans (subgroupOfEquivOfLe
      Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.s_le_l₁))
  let fB := (subgroupOfEquivOfLe hBX).symm.trans
    (fB₀.trans (subgroupOfEquivOfLe
      Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap.B_le_l₁))
  refine ⟨f,fT,fB,hfT,hfB,?_,?_⟩
  · intro t
    change ((fT₀ ((subgroupOfEquivOfLe hTX).symm t) : Jβ) :
      Sporadic.LeechRelated.J2.Carrier) = _
    rw [hfT₀]
    rfl
  · intro b
    change ((fB₀ ((subgroupOfEquivOfLe hBX).symm b) : Jβ) :
      Sporadic.LeechRelated.J2.Carrier) = _
    rw [hfB₀]
    rfl

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
