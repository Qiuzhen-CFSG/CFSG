module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBinaryResidualOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBinaryExactPathParameters

/-!
# The original binary exceptional/strict order split

The strict residual count supplies the order-sixty-four row. In the
exceptional row, the intrinsic core formulas force both cores to have
order sixteen; this excludes the field-four alternative in the established
marked recognition. The resulting case split starts with the original
F.1.11 critical pair and its literal binary beta quotient, and retains both
original and reduced exceptional amalgam inclusion squares and r=6, s=5.

The small-core application discharges D_alpha = Z_alpha from the bound
|Q_beta| ≤ 16. The strict irreducibility/quaternion clause and its path
parameters remain separate source obligations.

Source: DGS, Groups and Graphs (1985), (10.8)--(10.10), pp.161--165.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true
local notation "ι" => Subgroup.subtype (G₀ L S)

/-- The original binary beta quotient leaves exactly the exceptional
marked row or the strict order-sixty-four row. The D condition is decided
inside the theorem, and the exceptional branch retains both endpoint/Borel
inclusion squares and the literal path parameters. -/
theorem original_bTwo_binary_order_dichotomy
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) (hK : Nat.card K = 2) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    let D₀ := Q₁ ⊓ (Q F t).map ι
    let Z₀ := (Z F α).map ι
    (D₀ = Z₀ ∧ Nat.card D₀ = 4 ∧ Nat.card Q₀ = 16 ∧ Nat.card Q₁ = 16 ∧
      commonBorel L S = (commonBorel L S).pCoreIn 2 ∧
      Nat.card (commonBorel L S) = 32 ∧
      Nonempty (Theory.GroupTheory.RankTwoAmalgam.Iso
        (OriginalExtension.originalAmalgam L S).reverse
        Atlas.G2.BinaryParabolicPair.derivedAmalgam) ∧
      Nonempty (Theory.GroupTheory.RankTwoAmalgam.Iso
        (OriginalExtension.reducedAmalgam L S).reverse
        Atlas.G2.BinaryParabolicPair.derivedAmalgam) ∧
      HasSourcePathParameters
        (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 5) ∨
    (D₀ ≠ Z₀ ∧ Nat.card D₀ = 8 ∧ Nat.card Q₀ = 32 ∧ Nat.card Q₁ = 32 ∧
      Nat.card ((commonBorel L S).pCoreIn 2) = 64) := by
  classical
  by_cases hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι = (Z F α).map ι
  · obtain ⟨k,f,fin,ch,alg,c,hactor,hZD,hDQ,hDel,hZ,hQa,hQb,hlower,hiff,hstrict,
      hPhi,hder,hbound,hnP,hnB⟩ :=
      original_bTwo_intrinsic_core_orders h hc hne hb hβu ht htne e
    have hk : Nat.card k = 2 := by
      rw [hK] at hbound
      have : 1 < Nat.card k := Finite.one_lt_card
      omega
    have hDc : Nat.card ((parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι : Subgroup G) = 4 := by
      rw [hD,hZ,hk]
      norm_num
    have hQbc : Nat.card ((parabolic L S 1).pCoreIn 2) = 16 := by
      rw [hQb,hDc,hk,hK]
    rcases original_bTwo_exceptional_marked_selection h hc hne hb hβu ht htne hD with
      ⟨_,ha,hb',hfull,hB,hBc,hiso,hred⟩ | ⟨_,_,hbad,_⟩
    · exact Or.inl ⟨hD,hDc,ha,hb',hB,hBc,hiso,hred,
        original_bTwo_exceptional_path_parameters h hc hne hb hβu ht htne hD⟩
    · omega
  · obtain ⟨g,hg,hgt,hfour,hwhole,hRc,hDel,hdec,hdis,hprod,hZa,hZb,hDc,hQa,hQb,
      hB,hBc,hPhi,hder⟩ := original_bTwo_binary_strict_orders
        h hc hne hb hβu ht htne e hK hD
    exact Or.inr ⟨hD,hDc,hQa,hQb,hBc⟩

/-- A bound of sixteen on the binary beta core selects the actual
exceptional row. This discharges D=Z in the full original and reduced
binary recognition and in both source path parameters. -/
theorem original_bTwo_binary_small_core_marked_parameters
    (h : HypothesisF11 L S) {u t : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (ht : (graph F).Adj α t) (htne : t ≠ β)
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K)) (hK : Nat.card K = 2)
    (hsmall : Nat.card ((parabolic L S 1).pCoreIn 2) ≤ 16) :
    (parabolic L S 1).pCoreIn 2 ⊓ (Q F t).map ι = (Z F α).map ι ∧
      Nat.card ((parabolic L S 0).pCoreIn 2) = 16 ∧
      Nat.card ((parabolic L S 1).pCoreIn 2) = 16 ∧
      commonBorel L S = (commonBorel L S).pCoreIn 2 ∧
      Nat.card (commonBorel L S) = 32 ∧
      Nonempty (Theory.GroupTheory.RankTwoAmalgam.Iso
        (OriginalExtension.originalAmalgam L S).reverse
        Atlas.G2.BinaryParabolicPair.derivedAmalgam) ∧
      Nonempty (Theory.GroupTheory.RankTwoAmalgam.Iso
        (OriginalExtension.reducedAmalgam L S).reverse
        Atlas.G2.BinaryParabolicPair.derivedAmalgam) ∧
      HasSourcePathParameters
        (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 5 := by
  rcases original_bTwo_binary_order_dichotomy h hc hne hb hβu ht htne e hK with
    ⟨hD,_,hQa,hQb,hB,hBc,hiso,hred,hpath⟩ | ⟨_,_,_,hbad,_⟩
  · exact ⟨hD,hQa,hQb,hB,hBc,hiso,hred,hpath⟩
  · omega

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
