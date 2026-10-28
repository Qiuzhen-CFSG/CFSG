module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoIntrinsicCoreOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalMarkedSelection

/-!
# The order-32 beta core forces the exceptional field-four branch

For a beta field of order four, the intrinsic core order identity gives
|Q_beta| ≥ 4 q_alpha cubed. An upper bound of 32 forces q_alpha = 2 and
equality. The equality criterion therefore proves the literal original
D_alpha = Z_alpha, rather than retaining it as a recognition premise.

Applying the marked exceptional classification now gives the compatible
reduced J₂ and original J₂/Aut(J₂) amalgams and the exact path parameters.
This is the order-32 consumer; the independent source bound on that core
and the remaining strict Chapter 10 clauses are not asserted here.

Source: DGS, Groups and Graphs (1985), (10.7)--(10.9), printed pp.158--163.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open Noncommuting DGS85.Reduction Theory.GroupTheory
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true

/-- The field-four upper bound discharges the actual opposite-core equality. -/
theorem original_bTwo_field_four_small_core_eq_center
    (h : HypothesisF11 L S) {u t : Vertex F₀}
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆ ≠ ⊥)
    (hb : b F₀ = 2) (hβu : (graph F₀).Adj β u)
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) (hK : Nat.card K = 4)
    (hQ : Nat.card ((parabolic L S 1).pCoreIn 2) ≤ 32) :
    (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
        (Z F₀ α).map (G₀ L S).subtype ∧
      Nat.card ((parabolic L S 0).pCoreIn 2) = 64 ∧
      Nat.card ((parabolic L S 1).pCoreIn 2) = 32 := by
  obtain ⟨k,f,fin,ch,alg,c,hactor,hZD,hDQ,hDel,hZ,hQa,hQb,hlower,hiff,hstrict,
    hPhi,hder,hbound,hnP,hnB⟩ :=
    original_bTwo_intrinsic_core_orders h hc hne hb hβu ht htne e
  rw [hK] at hlower
  have hk : Nat.card k = 2 := by
    have hmin : 1 < Nat.card k := Finite.one_lt_card
    by_contra hne
    have hthree : 3 ≤ Nat.card k := by omega
    have hcub : 3^3 ≤ Nat.card k ^ 3 := Nat.pow_le_pow_left hthree 3
    norm_num at hcub
    omega
  rw [hk] at hlower
  norm_num at hlower
  have hQ32 : Nat.card ((parabolic L S 1).pCoreIn 2) = 32 := le_antisymm hQ hlower
  have hD := hiff.mpr (by simpa [hk,hK] using hQ32)
  refine ⟨hD,?_,hQ32⟩
  rw [hD,hZ,hk,hK] at hQa
  norm_num at hQa
  exact hQa

/-- The mixed order-32 consumer obtains both full marked alternatives and
path parameters without an assumed D=Z equality or a chosen natural action. -/
theorem original_bTwo_field_four_small_core_marked_parameters
    (h : HypothesisF11 L S) {u t : Vertex F₀}
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆ ≠ ⊥)
    (hb : b F₀ = 2) (hβu : (graph F₀).Adj β u)
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) (hK : Nat.card K = 4)
    (hQ : Nat.card ((parabolic L S 1).pCoreIn 2) ≤ 32) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    Q₁ ⊓ (Q F₀ t).map (G₀ L S).subtype = (Z F₀ α).map (G₀ L S).subtype ∧
      Nat.card Q₀ = 64 ∧ Nat.card Q₁ = 32 ∧
      IsExtraspecial 2 Q₁ ∧ Nonempty (Q₁ ≃* MinusExtraspecial.Model) ∧
      Nonempty (RankTwoAmalgam.Iso
        (OriginalExtension.reducedAmalgam L S).reverse
        GreenBook.HallJanko.j2Model.toMarking.amalgam) ∧
      (Nonempty (RankTwoAmalgam.Iso
          (OriginalExtension.originalAmalgam L S).reverse
          GreenBook.HallJanko.j2Model.toMarking.amalgam) ∨
        Nonempty (RankTwoAmalgam.Iso
          (OriginalExtension.originalAmalgam L S).reverse
          GreenBook.HallJanko.autJ2Model.toMarking.amalgam)) ∧
      HasSourcePathParameters
        (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 5 := by
  obtain ⟨hD,hQa,hQb⟩ := original_bTwo_field_four_small_core_eq_center
    h hc hne hb hβu ht htne e hK hQ
  obtain ⟨_,_,hex,hcore,hred,hiso,hpaths⟩ :=
    original_bTwo_exceptional_core_thirty_two_marked_parameters
      h hc hne hb hβu ht htne hD hQb
  exact ⟨hD,hQa,hQb,hex,hcore,hred,hiso,hpaths⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
