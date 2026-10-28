module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NilpotentFive.MixedPrimes
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Selection

/-!
# The nilpotent SL₂(5) branch of the outside products

The full outer group is nilpotent by the primary-coordinate calculation, so
its Sylow two-subgroup is normal. The literal chosen component K/O₂(K) therefore
supplies the outer premise of both Products and the residual-compatible
H-star Selection. There is no remaining normalizer, elementary-kernel,
center--Frattini, splitting, or mixed-prime hypothesis.

The ambient structural inputs, earlier geometry, normalizer containment and
11.3.2 input remain with `qt-d-1222-shadow-component-witness`, the owner of the
complete surviving-list assembly. This module proves the nilpotent model branch.
Source: Aschbacher--Smith A.3.6(4), pp.43--45; 11.1.1--2, pp.761--762;
11.4.3 and the subsequent selection, pp.778--779.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models

/-- The intrinsic hypotheses already suffice for the full outer calculation. -/
theorem nilpotentFive_outer_twoClosed_of_intrinsic
    {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    {𝒦 : GroupClass} (hQ : IsSQTK 𝒦 B)
    (hn : Chapter1.Section02.A36Nilpotent B) (hc : Chapter1.Section02.A36Common B) :
    ChapterE.IsTwoClosed (MulAut.Outer B) := by
  let := NilpotentFive.outer_nilpotent hQ hn hc
  exact ⟨Classical.arbitrary _, inferInstance⟩

/-- The exact conditional source contract, retaining the C-component and
trivial two-core hypotheses supplied by the ambient classification. -/
theorem nilpotentFive_outer_twoClosed
    {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    (_hC : (⊤ : Subgroup B).IsCComponent)
    (hQ : IsSQTK KnownSimple.IsKnownSimple B) (_hO : pCore 2 B = ⊥)
    (hn : Chapter1.Section02.A36Nilpotent B) (hc : Chapter1.Section02.A36Common B) :
    ChapterE.IsTwoClosed (MulAut.Outer B) :=
  nilpotentFive_outer_twoClosed_of_intrinsic hQ hn hc

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- The literal K/O₂(K) outer-group premise, now proved from its structural data. -/
theorem ofFlag_nilpotentFive_outer_twoClosed
    [Group.IsPerfect ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K)]
    (hQ : IsSQTK KnownSimple.IsKnownSimple
      ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K))
    (hn : Chapter1.Section02.A36Nilpotent
      ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K))
    (hc : Chapter1.Section02.A36Common
      ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K)) :
    ChapterE.IsTwoClosed
      (MulAut.Outer ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K)) :=
  nilpotentFive_outer_twoClosed_of_intrinsic hQ hn hc

/-- Both products of 11.4.3 in the full nilpotent SL₂(5) case. -/
theorem ofFlag_nilpotentFive_products
    [Group.IsPerfect ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K)]
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hQ : IsSQTK KnownSimple.IsKnownSimple
      ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K))
    (hn : Chapter1.Section02.A36Nilpotent
      ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K))
    (hc : Chapter1.Section02.A36Common
      ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K))
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    (∀ g ∈ Gz (ofFlag S f X z H),
      ∃ k ∈ (ofFlag S f X z H).K, ∃ y ∈ Yz (ofFlag S f X z H),
        ∃ m ∈ Mz (ofFlag S f X z H), g = k * y * m) ∧
    (∀ g ∈ (ofFlag S f X z H).G₁,
      ∃ k ∈ (ofFlag S f X z H).K, ∃ y ∈ (ofFlag S f X z H).Y,
        ∃ m ∈ (ofFlag S f X z H).M₁, g = k * y * m) := by
  have ho := ofFlag_nilpotentFive_outer_twoClosed S f X z H hQ hn hc
  exact ⟨point_product _ h he hNT ho, line_product _ h (f.invariant 0) hf hNT ho⟩

/-- The original residual-compatible H-star selection in the same full case. -/
theorem ofFlag_nilpotentFive_selected_H
    [Group.IsPerfect ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K)]
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hQ : IsSQTK KnownSimple.IsKnownSimple
      ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K))
    (hn : Chapter1.Section02.A36Nilpotent
      ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K))
    (hc : Chapter1.Section02.A36Common
      ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J) :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z H) ∧ SelectedResidualAlternative (ofFlag S f X z J) :=
  exists_selected_H _ h he hNT
    (ofFlag_nilpotentFive_outer_twoClosed S f X z H hQ hn hc) h1132

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models
