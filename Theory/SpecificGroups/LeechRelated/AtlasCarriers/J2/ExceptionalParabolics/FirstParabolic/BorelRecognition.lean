module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.SplitRecognition
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Overlap.Inner
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer

/-!
# Aligning the J₂ first endpoint with its Borel

Sylow conjugacy aligns a marked order-128 two-subgroup with the native Sylow
subgroup. Its order-384 normalizing overgroup must then be the native full
Sylow normalizer. Restricting the same endpoint equivalence gives the Borel
and Sylow maps and both inclusion squares.

Source: DGS, Groups and Graphs (1985), the J₂ parabolic exercise after
(10.9), p.163. This comparison concerns the first endpoint and its Borel;
the compatible second endpoint remains a separate obligation.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
open Seed
local notation "B₀" => SecondParabolic.Overlap.B

/-- Align an endpoint equivalence with the actual Sylow and full Borel. -/
theorem exists_borel_aligned_equiv {X : Type*} [Group X] [Finite X]
    (e : X ≃* l₁) (T B : Subgroup X)
    (hT : Nat.card T = 128) (hB : Nat.card B = 384)
    (hTB : B ≤ normalizer (T : Set X)) :
    ∃ f : X ≃* l₁, T.map f.toMonoidHom = s.subgroupOf l₁ ∧
      B.map f.toMonoidHom = (B₀).subgroupOf l₁ ∧
      ∃ (fT : T ≃* s.subgroupOf l₁) (fB : B ≃* (B₀).subgroupOf l₁),
        (∀ t : T, (fT t : l₁) = f (t : X)) ∧
        ∀ b : B, (fB b : l₁) = f (b : X) := by
  have hcard : Nat.card X = 1920 := (Nat.card_congr e.toEquiv).trans card_l₁
  have hi : T.index = 15 := by
    have hh := T.card_mul_index
    rw [hT,hcard] at hh
    omega
  let P : Sylow 2 X := (IsPGroup.of_card (n := 7) hT).toSylow (by rw [hi]; decide)
  let R : Sylow 2 l₁ := (SecondParabolic.sylow card_l₁).subtype SecondParabolic.s_le_l₁
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq l₁ (P.mapSurjective (f := e.toMonoidHom) e.surjective) R
  let f := e.trans (MulAut.conj g)
  have hfT : T.map f.toMonoidHom = s.subgroupOf l₁ := by
    have hh := congrArg Sylow.toSubgroup hg
    change (T.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = s.subgroupOf l₁ at hh
    change T.map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
    rw [←map_map]
    exact hh
  have hn : normalizer (s.subgroupOf l₁ : Set l₁) = (B₀).subgroupOf l₁ := by
    rw [←subgroupOf_normalizer_eq SecondParabolic.s_le_l₁,
      SecondParabolic.Overlap.normalizer_s_eq_B PairNormalizer.card_p₂]
  have hfB : B.map f.toMonoidHom = (B₀).subgroupOf l₁ := by
    have hle : B.map f.toMonoidHom ≤ (B₀).subgroupOf l₁ := by
      rw [←hn,←hfT,←map_normalizer_eq_of_bijective T f.bijective]
      exact map_mono hTB
    apply eq_of_le_of_card_ge hle
    rw [card_map_of_injective f.injective,
      Nat.card_congr (subgroupOfEquivOfLe SecondParabolic.Overlap.B_le_l₁).toEquiv,
      SecondParabolic.Overlap.card_B,hB]
  let fT := (T.equivMapOfInjective f.toMonoidHom f.injective).trans (MulEquiv.subgroupCongr hfT)
  let fB := (B.equivMapOfInjective f.toMonoidHom f.injective).trans (MulEquiv.subgroupCongr hfB)
  exact ⟨f,hfT,hfB,fT,fB,fun _ => rfl,fun _ => rfl⟩

end Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
