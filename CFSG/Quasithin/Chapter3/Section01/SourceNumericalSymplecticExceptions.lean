module
public import CFSG.Quasithin.Chapter3.Section01.SourceNumericalSmallExceptions
public import CFSG.Quasithin.Chapter3.Section01.SourceOddLinearOutside
/-!
# The remaining symplectic source geometry for the outside-core bound

For the original qrc action, the non-FF intersection span is elementary.
Consequently the normal elementary image bound removes the odd PSL3 row,
including the prime three. The only remaining source model is a proper
noncyclic central-plane image in a nonbinary symplectic component.

Source: Aschbacher--Smith E.2.7--13, printed pp.219--225, and the original
3.1.6 outside-core application, printed pp.573--574. The symplectic pair
recognition premise is retained explicitly; it is not a numerical conclusion.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The literal remaining symplectic quotient and its strict image-size range. -/
@[expose] def QrcHypotheses.HasSymplecticMiddleOutsideCoreModel
    (h : QrcHypotheses T M M₀ H V) : Prop :=
  ∃ hp : ChapterB.IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤,
  ∃ K : Subgroup H, K.IsCComponent ∧ K.Normal ∧
    K ⊔ ((T.subtype h.right_mem.1.1.2 : Sylow 2 H) : Subgroup H) = ⊤ ∧
    let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore (T.subtype h.right_mem.1.1.2) hp)
    ∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp (K.map q) 2 (2^f) ∧
      2 < Nat.card ((V.subgroupOf H).map q) ∧
      Nat.card ((V.subgroupOf H).map q) < (2^f)^2

/-- The original outside-core action has the cubic bound unless the remaining
symplectic pair-recognition case occurs. -/
theorem QrcHypotheses.outsideCore_cubicRatio_le_two_or_symplectic_middle_model
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hout : ¬ V ≤ H.pCoreIn 2) :
    letI := h.module_elementary
    cubicRatio (imageRepresentation M₀ V h.module_normalized) ≤ 2 ∨
      h.HasSymplecticMiddleOutsideCoreModel := by
  let := h.module_elementary
  rcases h.outsideCore_cubicRatio_le_two_or_small_exceptional_model hG hM hu hout with hb | hm
  · exact Or.inl hb
  obtain ⟨hp,K,hK,hN,hgen,htwo,hm⟩ := hm
  let := hN
  rcases hm with hodd | ⟨f,hf,hmodel,hcard⟩
  · exact Or.inl (h.odd_linear_cubicRatio_le_two hG hM hout hp K hK hgen
      (by decide : Nat.Prime 3) (by decide : Odd 3) hodd)
  · exact Or.inr ⟨hp,K,hK,hN,hgen,f,hf,hmodel,htwo,hcard⟩

end CFSG.Quasithin.Chapter3
