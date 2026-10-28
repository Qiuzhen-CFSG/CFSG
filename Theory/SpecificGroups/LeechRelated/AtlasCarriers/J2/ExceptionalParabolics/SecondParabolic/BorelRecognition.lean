module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.RootNormalizerModel
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Overlap.Inner
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer

/-!
# Aligning the J₂ second endpoint with its Borel

Sylow conjugacy aligns a marked order-128 two-subgroup with the native Sylow
subgroup. Its order-384 normalizing overgroup must then be the native full
Sylow normalizer. Restricting the same endpoint equivalence gives the Borel
and Sylow maps and both inclusion squares.

Source: DGS, Groups and Graphs (1985), the J₂ parabolic exercise after
(10.9), p.163. This comparison concerns the full second endpoint and its Borel;
agreement with the first endpoint on that Borel is a further obligation.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic
open Seed
local notation "B₀" => SecondParabolic.Overlap.B

/-- Align an endpoint equivalence with the actual Sylow and full Borel. -/
theorem exists_borel_aligned_equiv {X : Type*} [Group X] [Finite X]
    (e : X ≃* p₂) (T B : Subgroup X)
    (hT : Nat.card T = 128) (hB : Nat.card B = 384)
    (hTB : B ≤ normalizer (T : Set X)) :
    ∃ f : X ≃* p₂, T.map f.toMonoidHom = s.subgroupOf p₂ ∧
      B.map f.toMonoidHom = (B₀).subgroupOf p₂ ∧
      ∃ (fT : T ≃* s.subgroupOf p₂) (fB : B ≃* (B₀).subgroupOf p₂),
        (∀ t : T, (fT t : p₂) = f (t : X)) ∧
        ∀ b : B, (fB b : p₂) = f (b : X) := by
  have hcard : Nat.card X = 1152 := (Nat.card_congr e.toEquiv).trans PairNormalizer.card_p₂
  have hi : T.index = 9 := by
    have hh := T.card_mul_index
    rw [hT,hcard] at hh
    omega
  let P : Sylow 2 X := (IsPGroup.of_card (n := 7) hT).toSylow (by rw [hi]; decide)
  let R : Sylow 2 p₂ := (SecondParabolic.sylow FirstParabolic.card_l₁).subtype PairNormalizer.s_le_p₂
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq p₂ (P.mapSurjective (f := e.toMonoidHom) e.surjective) R
  let f := e.trans (MulAut.conj g)
  have hfT : T.map f.toMonoidHom = s.subgroupOf p₂ := by
    have hh := congrArg Sylow.toSubgroup hg
    change (T.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = s.subgroupOf p₂ at hh
    change T.map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
    rw [←map_map]
    exact hh
  have hn : normalizer (s.subgroupOf p₂ : Set p₂) = (B₀).subgroupOf p₂ := by
    rw [←subgroupOf_normalizer_eq PairNormalizer.s_le_p₂,
      SecondParabolic.Overlap.normalizer_s_eq_B PairNormalizer.card_p₂]
  have hfB : B.map f.toMonoidHom = (B₀).subgroupOf p₂ := by
    have hle : B.map f.toMonoidHom ≤ (B₀).subgroupOf p₂ := by
      rw [←hn,←hfT,←map_normalizer_eq_of_bijective T f.bijective]
      exact map_mono hTB
    apply eq_of_le_of_card_ge hle
    rw [card_map_of_injective f.injective,
      Nat.card_congr (subgroupOfEquivOfLe SecondParabolic.Overlap.B_le_p₂).toEquiv,
      SecondParabolic.Overlap.card_B,hB]
  let fT := (T.equivMapOfInjective f.toMonoidHom f.injective).trans (MulEquiv.subgroupCongr hfT)
  let fB := (B.equivMapOfInjective f.toMonoidHom f.injective).trans (MulEquiv.subgroupCongr hfB)
  exact ⟨f,hfT,hfB,fT,fB,fun _ => rfl,fun _ => rfl⟩

end Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic
