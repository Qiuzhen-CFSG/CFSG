module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.NaturalOdd.Outer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Selection

/-!
# The natural odd-kernel branch of the outside products

The actual perfect component with A.3.6's natural SL₂(p) kernel has nilpotent
outer group. This supplies the outer premise of both literal products and
the residual-compatible H-star selection on the original chosen flag.
The kernel and conjugation action are retained; no splitting, automorphism
coverage or outer-group hypothesis is imposed.

The preceding geometry and the original component classification remain
with qt-d-1222-shadow-component-witness; its final consumer is
qt-d-1222-shadow-components. This module discharges the complete natural
model calculation, including all primes allowed by A.3.6(3).
Source: Aschbacher--Smith A.3.6(3), pp.43--45; 11.4.3, pp.778--779.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models

/-- The intrinsic hypotheses already suffice for the full outer calculation. -/
theorem naturalOdd_outer_twoClosed_of_intrinsic
    {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    (hn : Chapter1.Section02.A36Natural B) :
    ChapterE.IsTwoClosed (MulAut.Outer B) := by
  let := NaturalOdd.outer_nilpotent hn
  exact ⟨Classical.arbitrary _, inferInstance⟩

/-- The exact conditional source contract, retaining the C-component and
trivial two-core hypotheses supplied by the ambient classification. -/
theorem naturalOdd_outer_twoClosed
    {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
    (_hC : (⊤ : Subgroup B).IsCComponent)
    (_hQ : IsSQTK KnownSimple.IsKnownSimple B) (_hO : pCore 2 B = ⊥)
    (hn : Chapter1.Section02.A36Natural B) (_hc : Chapter1.Section02.A36Common B) :
    ChapterE.IsTwoClosed (MulAut.Outer B) :=
  naturalOdd_outer_twoClosed_of_intrinsic hn

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- The literal K/O₂(K) outer-group premise, now proved from its structural data. -/
theorem ofFlag_naturalOdd_outer_twoClosed
    [Group.IsPerfect ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K)]
    (hn : Chapter1.Section02.A36Natural
      ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K)) :
    ChapterE.IsTwoClosed
      (MulAut.Outer ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K)) :=
  naturalOdd_outer_twoClosed_of_intrinsic hn

/-- Both products of 11.4.3 in the full natural SL₂(p) case. -/
theorem ofFlag_naturalOdd_products
    [Group.IsPerfect ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K)]
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hn : Chapter1.Section02.A36Natural
      ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K))
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    (∀ g ∈ Gz (ofFlag S f X z H),
      ∃ k ∈ (ofFlag S f X z H).K, ∃ y ∈ Yz (ofFlag S f X z H),
        ∃ m ∈ Mz (ofFlag S f X z H), g = k * y * m) ∧
    (∀ g ∈ (ofFlag S f X z H).G₁,
      ∃ k ∈ (ofFlag S f X z H).K, ∃ y ∈ (ofFlag S f X z H).Y,
        ∃ m ∈ (ofFlag S f X z H).M₁, g = k * y * m) := by
  have ho := ofFlag_naturalOdd_outer_twoClosed S f X z H hn
  exact ⟨point_product _ h he hNT ho, line_product _ h (f.invariant 0) hf hNT ho⟩

/-- The original residual-compatible H-star selection in the same full case. -/
theorem ofFlag_naturalOdd_selected_H
    [Group.IsPerfect ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K)]
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hn : Chapter1.Section02.A36Natural
      ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J) :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z H) ∧ SelectedResidualAlternative (ofFlag S f X z J) :=
  exists_selected_H _ h he hNT
    (ofFlag_naturalOdd_outer_twoClosed S f X z H hn) h1132

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models
