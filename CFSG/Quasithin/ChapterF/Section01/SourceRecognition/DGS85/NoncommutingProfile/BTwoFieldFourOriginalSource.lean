module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourReducedSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwo

/-!
# Applying reduced field-four recognition to the original pair

The constructed full reduced beta endpoint is the native perfect J₂
involution centralizer. Its original local factor is therefore the whole
reduced endpoint. Apply the existing original-extension theorems to this
actual comparison: the beta core quotient is A₅ or S₅, and a single index
one or two controls both endpoint extensions, the full Borel and the
original Sylow subgroup. Thus the corresponding Borel orders are 384 or
768 and the Sylow orders are 128 or 256.

No parabolic comparison is an input here. The map-level reduced comparison
is constructed from the original center, commutator and field-four source
hypotheses. The compatible alpha endpoint, outer endpoint maps, and all
remaining Chapter 10 path and residual arguments retain their obligations.
Source: DGS, Groups and Graphs (1985), (10.9), p.163 and (15.3), pp.229--231;
Aschbacher--Smith F.1.11--12, pp.262--264.
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
local instance fieldFourOriginalAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

open SuzukiContainment

open GreenBook

/-- Apply the recognized reduced beta endpoint to the full original pair.
The same extension index controls both endpoints, the full Borel and S. -/
theorem original_bTwo_field_four_original_extension
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
    L 1 = P₀ L S 1 ∧
      parabolic L S 1 = L 1 ⊔ S ∧
      twoCore (L 1) = twoCore (parabolic L S 1) ∧
      Nat.card (pCore 2 (L 1)) = 32 ∧
      (Nonempty ((parabolic L S 1 ⧸ pCore 2 (parabolic L S 1)) ≃*
          alternatingGroup (Fin 5)) ∨
        Nonempty ((parabolic L S 1 ⧸ pCore 2 (parabolic L S 1)) ≃*
          Equiv.Perm (Fin 5))) ∧
      ∃ n : ℕ, (n = 1 ∨ n = 2) ∧
        (B₀ L S).relIndex (commonBorel L S) = n ∧
        (∀ i : Fin 2, (P₀ L S i).relIndex (parabolic L S i) = n) ∧
        Nat.card (parabolic L S 1) = 1920 * n ∧
        Nat.card (commonBorel L S) = 384 * n ∧ Nat.card S = 128 * n := by
  obtain ⟨f,fB,fT,hfB,hfT,d,hd⟩ := original_bTwo_field_four_reduced_beta_borel_equiv
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  let eP : parabolic L (reducedSylow L S) 1 ≃* HallJanko.j2Model.toMarking.P 0 :=
    ((MulEquiv.subgroupCongr (P₀_eq_source h 1).symm).trans f).trans
      (MulEquiv.subgroupCongr HallJanko.j2Model_P_zero.symm)
  have hL : L 1 = P₀ L S 1 :=
    (OriginalExtension.JankoTwo.local_eq_reduced h 1 eP).trans (P₀_eq_source h 1).symm
  have hi := OriginalExtension.JankoTwo.original_borel_index_cases h 1 eP
  rw [←B₀_eq_source h] at hi
  let n := (B₀ L S).relIndex (commonBorel L S)
  have hpi (i : Fin 2) : (P₀ L S i).relIndex (parabolic L S i) = n := by
    rw [P₀_eq_source h i,OriginalExtension.parabolic_extension_index h i,←B₀_eq_source h]
  obtain ⟨_,_,hP,hB⟩ := original_bTwo_field_four_reduced_beta_equals_enlargement
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  have hp := relIndex_mul_relIndex (⊥ : Subgroup G) (P₀ L S 1)
    (parabolic L S 1) bot_le (P₀_le h 1)
  rw [relIndex_bot_left,relIndex_bot_left,hP,hpi] at hp
  have hbc := relIndex_mul_relIndex (⊥ : Subgroup G) (B₀ L S)
    (commonBorel L S) bot_le (B₀_le h)
  rw [relIndex_bot_left,relIndex_bot_left,hB] at hbc
  have hs := OriginalExtension.original_sylow_card h
  rw [OriginalExtension.JankoTwo.reduced_sylow_card h 1 eP,←B₀_eq_source h] at hs
  exact ⟨hL,OriginalExtension.JankoTwo.original_first_eq_sup h 1 eP,
    (OriginalExtension.JankoTwo.original_core_eq_local h 1 eP).symm,
    OriginalExtension.JankoTwo.local_core_card h 1 eP,
    OriginalExtension.JankoTwo.original_first_quotient h 1 eP,
    n,hi,rfl,hpi,hp.symm,hbc.symm,hs⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
