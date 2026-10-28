module
public import Theory.SpecificGroups.LieType.F4RootSL2.Elementary
public import Theory.SpecificGroups.LieType.F4RootSL2.Separation
public import Theory.GroupTheory.CentralQuotientSquare
public import Theory.SpecificGroups.LieType.F4OddFundamentalCentralizer

/-!
# The literal proper fundamental SL₂ in F₄

Compose the faithful long-root matrix action with the actual central
projection defining `ExceptionalSplit.F4`. Its upper and lower transvections
are exactly the canonical root curves at ±α₀, and its range is the existing
`f4FundamentalRootPair` at this long simple root.

An element killed by the projection is central in SL₂, hence is 1 or −1.
The explicit neighboring-root matrix calculation excludes −1. Moreover the
image of −1 is noncentral even after taking the quotient: otherwise a square
root of the neighboring root element, together with the involution identity,
would force the original matrices to commute. Since −1 is central in SL₂,
this also proves that the range is proper, without an order formula. All
results hold over every field with 2 ≠ 0, including every finite odd field.

Source: the proper fundamental subgroup K*₀ ≅ SL₂(q) in Aschbacher–Smith
A.2.17, printed p.39 of `refs/quasithin.pdf`, citing Asc80, p.401;
the integral subsystem construction is GLS3 §§1.12 and 2.6
(`refs/KGroup/GLS3/chapter2.tex`). The complementary Sp₆ residual-centralizer
identification is a separate theorem and is not assumed here.
-/

@[expose] public noncomputable section
namespace ExceptionalSplit.F4RootSL2
open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _
local instance : InvolutiveNeg typeF4Roots := typeF4RootPairing.indexNeg
variable {F : Type*} [Field F]

/-- The literal fundamental map, through the elementary adjoint group and its center quotient. -/
def hom : SL(2, F) →* F4 F :=
  (projection typeF4RootPairing typeF4RootPairing_base F).comp elementaryHom

@[simp] theorem hom_upper (t : F) : hom (upper t) =
    rootElement typeF4RootPairing typeF4RootPairing_base F fundamentalRoot t := by
  change projection _ _ F (elementaryHom (upper t)) = _
  rw [elementaryHom_upper]
  rfl

@[simp] theorem hom_lower (t : F) : hom (lower t) =
    rootElement typeF4RootPairing typeF4RootPairing_base F
      (-fundamentalRoot : typeF4Roots) t := by
  change projection _ _ F (elementaryHom (lower t)) = _
  rw [elementaryHom_lower]
  rfl

private abbrev neighbor (t : F) : Elementary F :=
  elementaryRoot typeF4RootPairing typeF4RootPairing_base F neighborRoot t

private lemma neighbor_val (t : F) : (neighbor t).val =
    positiveUnit neighborRoot t := rootCurveUnit_simple neighborRoot t

private lemma elementary_neg_one_not_commute (hF : (2 : F) ≠ 0) :
    ¬ Commute (elementaryHom (-1 : SL(2, F))) (neighbor 1) := by
  intro h
  apply neg_one_not_commute_neighbor hF
  have hh := congrArg Subtype.val h.eq
  change ambientHom (-1 : SL(2, F)) * (neighbor 1).val =
    (neighbor 1).val * ambientHom (-1 : SL(2, F)) at hh
  simpa only [neighbor_val, neighborRoot, commute_iff_eq] using hh

/-- The central involution in SL₂ is not central in the elementary F₄ group. -/
theorem elementaryHom_neg_one_not_mem_center (hF : (2 : F) ≠ 0) :
    elementaryHom (-1 : SL(2, F)) ∉ Subgroup.center (Elementary F) := by
  intro h
  exact elementary_neg_one_not_commute hF
    (Subgroup.mem_center_iff.mp h (neighbor 1)).symm

/-- Quotienting by the center does not kill the long-root involution. -/
theorem hom_neg_one_ne_one (hF : (2 : F) ≠ 0) :
    hom (-1 : SL(2, F)) ≠ 1 := by
  intro h
  exact elementaryHom_neg_one_not_mem_center hF
    ((projection_eq_one_iff _ _ F _).mp h)

/-- The long-root involution is still noncentral in the actual quotient. -/
theorem hom_neg_one_not_mem_center (hF : (2 : F) ≠ 0) :
    hom (-1 : SL(2, F)) ∉ Subgroup.center (F4 F) := by
  intro h
  let x : Elementary F := neighbor ((2 : F)⁻¹)
  have hx : x ^ 2 = neighbor 1 := by
    change neighbor ((2 : F)⁻¹) ^ 2 = _
    rw [pow_two, neighbor, ← elementaryRoot_add]
    congr 1
    field_simp [hF]
    norm_num
  have hz : elementaryHom (-1 : SL(2, F)) ^ 2 = 1 := by
    rw [← map_pow]
    simp
  have hc : Commute (QuotientGroup.mk' (Subgroup.center (Elementary F)) x)
      (QuotientGroup.mk' (Subgroup.center (Elementary F)) (elementaryHom (-1))) :=
    Subgroup.mem_center_iff.mp h _
  have he := Subgroup.commute_square_of_centralQuotient_commute hz hc
  rw [hx] at he
  exact elementary_neg_one_not_commute hF he.symm

private lemma sl2_center_cases {g : SL(2, F)}
    (hg : g ∈ Subgroup.center SL(2, F)) : g = 1 ∨ g = -1 := by
  obtain ⟨a, ha, h⟩ := SpecialLinearGroup.mem_center_iff.mp hg
  simp only [Fintype.card_fin] at ha
  rcases sq_eq_one_iff.mp ha with rfl | rfl
  · left
    apply Subtype.ext
    simpa using h.symm
  · right
    apply Subtype.ext
    simpa [← Matrix.diagonal_neg] using h.symm

/-- Faithfulness survives the literal central projection, over every odd-characteristic field. -/
theorem hom_injective (hF : (2 : F) ≠ 0) : Function.Injective (hom (F := F)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  have hc : elementaryHom g ∈ Subgroup.center (Elementary F) :=
    (projection_eq_one_iff _ _ F _).mp hg
  have hgcenter : g ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro a
    apply elementaryHom_injective
    simpa only [map_mul] using Subgroup.mem_center_iff.mp hc (elementaryHom a)
  rcases sl2_center_cases hgcenter with h | rfl
  · exact h
  · exact (hom_neg_one_ne_one hF hg).elim

/-- The range is exactly the two specified opposite root curves' generated subgroup. -/
theorem hom_range : (hom (F := F)).range = f4FundamentalRootPair fundamentalRoot := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    apply Matrix.SL2.transvection_induction
      (fun g => hom g ∈ f4FundamentalRootPair fundamentalRoot) ?_ ?_ g
    · intro i j hij t
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · change hom (upper t) ∈ _
        rw [hom_upper]
        exact f4FundamentalRootPair_mem _ t
      · change hom (lower t) ∈ _
        rw [hom_lower]
        exact f4FundamentalRootPair_neg_mem _ t
      · exact (hij rfl).elim
    · intro A B hA hB
      rw [map_mul]
      exact Subgroup.mul_mem _ hA hB
  · apply (Subgroup.closure_le _).mpr
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact ⟨upper t, hom_upper t⟩
    · exact ⟨lower t, hom_lower t⟩

/-- The fundamental SL₂ is proper, without a group-order calculation. -/
theorem hom_range_ne_top (hF : (2 : F) ≠ 0) : (hom (F := F)).range ≠ ⊤ := by
  intro h
  apply hom_neg_one_not_mem_center hF
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨g, rfl⟩ := MonoidHom.range_eq_top.mp h y
  rw [← map_mul, ← map_mul]
  congr 1
  simp

/-- The source's literal root-pair subgroup is proper. -/
theorem fundamentalRootPair_ne_top (hF : (2 : F) ≠ 0) :
    f4FundamentalRootPair (F := F) fundamentalRoot ≠ ⊤ := by
  rw [← hom_range]
  exact hom_range_ne_top hF

/-- The actual SL₂ identification of the fundamental root-pair carrier. -/
def fundamentalEquiv (hF : (2 : F) ≠ 0) :
    SL(2, F) ≃* f4FundamentalRootPair (F := F) fundamentalRoot :=
  (MonoidHom.ofInjective (hom_injective hF)).trans (MulEquiv.subgroupCongr hom_range)

end ExceptionalSplit.F4RootSL2

end
