module
public import Theory.SpecificGroups.Janko1.Model.BinaryDegree
public import Theory.Representation.CentralizerQuotientAction
public import Theory.GroupTheory.NormalizedSupCard
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPair

/-!
# The J₁ obstruction on the actual pair span

Two original A₅ block modules each have sixteen elements. When their
join is elementary, the subgroup product formula bounds its order by
256, hence its binary dimension by eight. Its canonical centralizer
quotient acts faithfully, so no subgroup of that quotient is J₁: the
checked element of order eleven requires dimension at least ten.

This supplies the literal small-span exclusion used in the last
non-A₃ case of C.5.12, Aschbacher–Smith, printed p.163. The earlier
component placement and two-conjugate generation remain with the
source embedding argument.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
variable {G : Type*} [Group G] [Finite G]
/-- Two conjugate elementary modules of order sixteen span at most eight binary dimensions. -/
theorem four_pair_span_rank (U : Subgroup G) (hU : Nat.card U = 16) (g : G)
    (X : Subgroup G) (hVX : U ⊔ U.conjBy g ≤ X)
    [IsElementaryAbelian 2 (U ⊔ U.conjBy g : Subgroup G)] :
    let : IsElementaryAbelian 2 ((U ⊔ U.conjBy g).subgroupOf X) := IsElementaryAbelian.subgroupOf hVX
    Module.finrank (ZMod 2) (Additive ((U ⊔ U.conjBy g).subgroupOf X)) ≤ 8 := by
  let V := U ⊔ U.conjBy g
  let : IsElementaryAbelian 2 (V.subgroupOf X) := IsElementaryAbelian.subgroupOf hVX
  have hUc : U.conjBy g ≤ centralizer (U : Set G) := by
    intro w hw u hu
    exact congrArg V.subtype (mul_comm (⟨u,mem_sup_left hu⟩ : V) ⟨w,mem_sup_right hw⟩)
  have hW : Nat.card (U.conjBy g) = 16 :=
    (Nat.card_congr (U.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv).symm.trans hU
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes U (U.conjBy g)
    (hUc.trans (Subgroup.centralizer_le_normalizer _))
  have hpos : 0 < Nat.card (U ⊓ U.conjBy g : Subgroup G) := Nat.card_pos
  have hcV : Nat.card V ≤ 256 := by
    rw [hU,hW] at hc
    change Nat.card (U ⊔ U.conjBy g : Subgroup G) ≤ 256
    nlinarith
  have he : Nat.card (Additive (V.subgroupOf X)) = Nat.card V :=
    (Nat.card_congr Additive.toMul).trans (Nat.card_congr (subgroupOfEquivOfLe hVX).toEquiv)
  have hn : Nat.card (Additive (V.subgroupOf X)) =
      2 ^ Module.finrank (ZMod 2) (Additive (V.subgroupOf X)) := by
    simpa only [Nat.card_eq_fintype_card,ZMod.card] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (V.subgroupOf X)))
  have hp : 2 ^ Module.finrank (ZMod 2) (Additive (V.subgroupOf X)) ≤ 2 ^ 8 := by
    rw [← hn,he]
    exact hcV
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp hp

open ConjugateSource
/-- Two original four-dimensional block modules do not admit a J₁
subgroup in their canonical faithful action quotient. -/
theorem alternating_pair_span_excludes_janko
    {R K L : Subgroup G} (h : AlternatingPairSetup R K L)
    (g : G) (X : Subgroup G)
    (hVX : sourceModule K ⊔ (sourceModule K).conjBy g ≤ X)
    (hXV : X ≤ normalizer ((sourceModule K ⊔ (sourceModule K).conjBy g : Subgroup G) : Set G))
    [IsElementaryAbelian 2 (sourceModule K ⊔ (sourceModule K).conjBy g : Subgroup G)] :
    let V := sourceModule K ⊔ (sourceModule K).conjBy g
    let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
    let : IsElementaryAbelian 2 (V.subgroupOf X) := IsElementaryAbelian.subgroupOf hVX
    ∀ J : Subgroup (X ⧸ centralizer (V.subgroupOf X : Set X)),
      ¬ Nonempty (J ≃* Janko1.Model) := by
  let V := sourceModule K ⊔ (sourceModule K).conjBy g
  let : (V.subgroupOf X).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let : IsElementaryAbelian 2 (V.subgroupOf X) := IsElementaryAbelian.subgroupOf hVX
  dsimp only
  rintro J ⟨e⟩
  let ρ := Representation.centralizerQuotient (V.subgroupOf X)
  have hi : Function.Injective ρ := by
    intro a b hab
    apply Representation.centralizerQuotient_faithful _
    exact Units.ext hab
  let σ := ρ.comp (J.subtype.comp e.symm.toMonoidHom)
  have hs : Function.Injective σ := hi.comp (J.subtype_injective.comp e.symm.injective)
  have hlo := Janko1.ten_le_binary_finrank σ hs
  have hhi := four_pair_span_rank (sourceModule K) h.module_card g X hVX
  change Module.finrank (ZMod 2) (Additive (V.subgroupOf X)) ≤ 8 at hhi
  omega
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
