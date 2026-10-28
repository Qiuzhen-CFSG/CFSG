module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Selection
public import Theory.SpecificGroups.PSL2.OuterSolvable.BinaryCyclic
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage

/-!
# The rank-one outer groups in the surviving component list

For K=L₁ the original flag quotient is PSL₂ over the original binary field.
Its outer group is cyclic by inner-field automorphism coverage. In the prime
PSL₂ alternative the full outer group is a two-group. Transport uses actual
isomorphisms of K/O₂(K), and hence of their outer automorphism groups.

Both branches feed the point and line products and the residual-compatible
selection of H on the same chosen flag. The preceding flag quotient, local
geometry, Kz=K, fixed-space vanishing, Sylow-normalizer bound and full 11.3.2
remain explicit. Their producers are the natural local geometry, shadow
linear geometry, component triangle and comparison tasks. No outer-action
premise remains in the consumers here.

This is not the entire 11.4.3 assembly: the odd-by-SL₂ alternative must retain
its odd kernel and is not identified with the prime PSL₂ quotient. In
particular the partial ClassicalRefinementCase is not used as an exhaustive
source list.

Source: Aschbacher--Smith, §§11.1 and 11.4.3, printed pp.760--762 and 778;
the H-selection after 11.5.1 is on printed p.779.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models

private theorem twoClosed_of_cyclic {A : Type*} [Group A] [Finite A] [IsCyclic A] :
    ChapterE.IsTwoClosed A := by
  let P : Sylow 2 A := Classical.choice inferInstance
  exact ⟨P, inferInstance⟩

private theorem twoClosed_of_twoGroup {A : Type*} [Group A] (h : IsPGroup 2 A) :
    ChapterE.IsTwoClosed A := by
  let P : Sylow 2 A := (h.to_subgroup ⊤).toSylow (by simp)
  exact ⟨P, inferInstanceAs (⊤ : Subgroup A).Normal⟩

private theorem binary_outer_twoClosed {A : Type*} [Group A] [Finite A]
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : A ≃* Theory.PSL2.Group F) : ChapterE.IsTwoClosed (MulAut.Outer A) := by
  let : IsCyclic (MulAut.Outer (Theory.PSL2.Group F)) :=
    Theory.PSL2.OuterSolvable.outer_isCyclic_of_field_coverage
      BenderSuzuki.ZD.Linear.semilinear_coverage
  let : IsCyclic (MulAut.Outer A) :=
    isCyclic_of_surjective (MulAut.outerCongr e).symm
      (MulAut.outerCongr e).symm.surjective
  exact twoClosed_of_cyclic

private theorem prime_outer_twoClosed {A : Type*} [Group A] [Finite A] {p : ℕ}
    (hp : p.Prime) (hlarge : 3 < p) (hm : ClassicalGroup.IsPSL A 2 p) :
    ChapterE.IsTwoClosed (MulAut.Outer A) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  have ho := Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two
    hp (hp.odd_of_ne_two (by omega)) (n := 1) (by decide)
    (show Nat.card F = p ^ 1 by simpa using hcard)
  exact twoClosed_of_twoGroup (ho.of_equiv (MulAut.outerCongr e).symm)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- The equality branch uses the actual first flag-residual quotient over
the original source field, not merely a rank-one family label. -/
theorem ofFlag_equal_outer_twoClosed
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hm : Nonempty ((f.Li 0 ⧸ pCore 2 (f.Li 0)) ≃* Theory.PSL2.Group S.field.Carrier)) :
    ChapterE.IsTwoClosed
      (MulAut.Outer ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K)) := by
  rw [hK]
  exact binary_outer_twoClosed hm.some

/-- The prime-field alternative supplies a two-group, hence a normal Sylow,
in the full actual outer group of K/O₂(K). -/
theorem ofFlag_prime_outer_twoClosed {p : ℕ} (hp : p.Prime) (hlarge : 11 ≤ p)
    (hm : ClassicalGroup.IsPSL
      ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K) 2 p) :
    ChapterE.IsTwoClosed
      (MulAut.Outer ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K)) :=
  prime_outer_twoClosed hp (by omega) hm

/-- Both literal products in 11.4.3 when the first component equals L₁.
The outer-group hypothesis of Products is discharged by the binary model. -/
theorem ofFlag_equal_products
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hm : Nonempty ((f.Li 0 ⧸ pCore 2 (f.Li 0)) ≃* Theory.PSL2.Group S.field.Carrier))
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    (∀ g ∈ Gz (ofFlag S f X z H),
      ∃ k ∈ (ofFlag S f X z H).K, ∃ y ∈ Yz (ofFlag S f X z H),
        ∃ m ∈ Mz (ofFlag S f X z H), g = k * y * m) ∧
    (∀ g ∈ (ofFlag S f X z H).G₁,
      ∃ k ∈ (ofFlag S f X z H).K, ∃ y ∈ (ofFlag S f X z H).Y,
        ∃ m ∈ (ofFlag S f X z H).M₁, g = k * y * m) := by
  have ho := ofFlag_equal_outer_twoClosed S f X z H hK hm
  exact ⟨point_product _ h he hNT ho, line_product _ h (f.invariant 0) hf hNT ho⟩

/-- Both literal products in the surviving prime PSL₂ case. -/
theorem ofFlag_prime_products
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    {p : ℕ} (hp : p.Prime) (hlarge : 11 ≤ p)
    (hm : ClassicalGroup.IsPSL
      ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K) 2 p)
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    (∀ g ∈ Gz (ofFlag S f X z H),
      ∃ k ∈ (ofFlag S f X z H).K, ∃ y ∈ Yz (ofFlag S f X z H),
        ∃ m ∈ Mz (ofFlag S f X z H), g = k * y * m) ∧
    (∀ g ∈ (ofFlag S f X z H).G₁,
      ∃ k ∈ (ofFlag S f X z H).K, ∃ y ∈ (ofFlag S f X z H).Y,
        ∃ m ∈ (ofFlag S f X z H).M₁, g = k * y * m) := by
  have ho := ofFlag_prime_outer_twoClosed S f X z H hp hlarge hm
  exact ⟨point_product _ h he hNT ho, line_product _ h (f.invariant 0) hf hNT ho⟩

/-- The source H-star selection in the equality branch, with O²(H) in
both residual clauses and with no extra outer-action input. -/
theorem ofFlag_equal_selected_H
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hm : Nonempty ((f.Li 0 ⧸ pCore 2 (f.Li 0)) ≃* Theory.PSL2.Group S.field.Carrier))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J) :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z H) ∧ SelectedResidualAlternative (ofFlag S f X z J) :=
  exists_selected_H _ h he hNT (ofFlag_equal_outer_twoClosed S f X z H hK hm) h1132

/-- The same residual-compatible selection in the prime PSL₂ branch. -/
theorem ofFlag_prime_selected_H
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    {p : ℕ} (hp : p.Prime) (hlarge : 11 ≤ p)
    (hm : ClassicalGroup.IsPSL
      ((ofFlag S f X z H).K ⧸ pCore 2 (ofFlag S f X z H).K) 2 p)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J) :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z H) ∧ SelectedResidualAlternative (ofFlag S f X z J) :=
  exists_selected_H _ h he hNT (ofFlag_prime_outer_twoClosed S f X z H hp hlarge hm) h1132

/-- The final clause of 11.4.3(1) in the equality branch: the actual
quotient centralizer in Gz escapes M. -/
theorem ofFlag_equal_kernel_outside
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hm : Nonempty ((f.Li 0 ⧸ pCore 2 (f.Li 0)) ≃* Theory.PSL2.Group S.field.Carrier))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J) :
    ¬ Yz (ofFlag S f X z H) ≤ normalizer (L : Set G) :=
  kernel_outside_of_equal _ h he hNT
    (ofFlag_equal_outer_twoClosed S f X z H hK hm) h1132 hK

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models
