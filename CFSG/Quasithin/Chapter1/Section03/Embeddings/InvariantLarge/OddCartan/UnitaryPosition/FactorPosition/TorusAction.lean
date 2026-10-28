module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.FactorPosition.Inverter
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.FactorPosition.TorusAction.MatrixReduction
public import Theory.Representation.RankThreeDeterminantCentralizer

/-!
# The unitary Cartan action of a normalizing two-subgroup

The cross-characteristic, noncyclic abelian subgroup B lifts faithfully to
special unitary matrices. The matrix reduction gives an abelian centralizer
and a normalizer/centralizer index dividing six. The relative centralizer in
the normalizing two-subgroup S ∩ D consequently has index dividing two.

The determinant-one centralizer theorem supplies the matrix premise: noncyclicity
forces three distinct character lines, so centralizing matrices commute.
`caseThree_torus_action` discharges this premise in the original conditional
reduction. Normalization of B by S ∩ D remains the separately supplied hypothesis;
the factor-position assembly is responsible for proving it.

Source: Aschbacher--Smith, A.3.15(3), printed pp.50--51; A.3.21(c), printed
pp.55--56; and the proof of 1.3.4, printed pp.510--511 of refs/quasithin.pdf.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition

private theorem two_subgroup_centralizer_index {G : Type*} [Group G] [Finite G]
    (B T : Subgroup G) (hT : IsPGroup 2 T) (hn : T ≤ normalizer B)
    (hsix : (centralizer (B : Set G)).relIndex (normalizer B) ∣ 6) :
    ((centralizer (B : Set G)).subgroupOf T).index ∣ 2 := by
  let C := (centralizer (B : Set G)).subgroupOf (normalizer B)
  have hd : ((centralizer (B : Set G)).subgroupOf T).index ∣ C.index := by
    change (centralizer (B : Set G)).relIndex T ∣ C.index
    rw [← relIndex_subgroupOf hn]
    exact C.relIndex_dvd_index_of_normal _
  obtain ⟨n, hncard⟩ := hT.exists_card_eq
  have hp : ((centralizer (B : Set G)).subgroupOf T).index ∣ 2 ^ n :=
    hncard ▸ ((centralizer (B : Set G)).subgroupOf T).index_dvd_card
  exact ((Nat.Coprime.pow_left n (by decide : Nat.Coprime 2 3)).of_dvd_left hp).dvd_of_dvd_mul_right
    (hd.trans hsix)

/-- Torus-action reduction with an explicit matrix-centralizer premise.
`caseThree_torus_action` supplies it using the determinant-one theorem. -/
theorem caseThree_torus_action_of_matrix_centralizers
    {J : Type*} [Group J] [Finite J]
    {κ : GroupClass} {D B K : Subgroup J} {S : Sylow 2 J} {p q : ℕ}
    [Fact q.Prime] (hA : AmbientInput κ D B S p)
    (hC : CaseThree D B (S : Subgroup J) K q .unitary .unitary)
    (hn : ¬ IsCyclic B) (_hlarge : 3 < q)
    (hnorm : (S : Subgroup J) ⊓ D ≤ normalizer B)
    (hcent : ∀ (F : Type) [Field F] [Finite F] (R : Subgroup (GL (Fin 3) F)),
      IsMulCommutative R → (Nat.card R : F) ≠ 0 → ¬ IsCyclic R →
      (∀ x : R, Matrix.GeneralLinearGroup.det x.val = 1) →
      IsMulCommutative (centralizer (R : Set (GL (Fin 3) F)))) :
    IsMulCommutative ((centralizer (B : Set J)).subgroupOf ((S : Subgroup J) ⊓ D)) ∧
      ((centralizer (B : Set J)).subgroupOf ((S : Subgroup J) ⊓ D)).index ∣ 2 := by
  let _ : Fact p.Prime := ⟨hA.prime⟩
  let _ : IsMulCommutative B := hC.toCyclicDecomposition.isMulCommutative
  let B₀ := B.subgroupOf D
  let T : Subgroup J := (S : Subgroup J) ⊓ D
  let T₀ := T.subgroupOf D
  have hB₀p : IsPGroup p B₀ := hA.p_group.of_equiv (subgroupOfEquivOfLe hA.inside).symm
  have hB₀n : ¬ IsCyclic B₀ := fun hc => hn ((subgroupOfEquivOfLe hA.inside).isCyclic.mp hc)
  have hTp : IsPGroup 2 T := S.isPGroup'.of_injective
    (inclusion inf_le_left) (inclusion_injective inf_le_left)
  have hT₀p : IsPGroup 2 T₀ := hTp.of_equiv
    (subgroupOfEquivOfLe (show T ≤ D from inf_le_right)).symm
  have hT₀n : T₀ ≤ normalizer B₀ := by
    intro x hx
    apply mem_normalizer_iff.mpr
    intro b
    change (b : J) ∈ B ↔ ((x : J) * b * (x : J)⁻¹) ∈ B
    exact mem_normalizer_iff.mp (hnorm hx) b
  obtain ⟨hcomm, hindex⟩ := isPSU_centralizer_bound_of_matrix_centralizers
    (p := p) (q := q) (by have := hA.large; omega)
    (caseThree_prime_ne_characteristic hA hC hn) hC.model B₀ hB₀p hB₀n hcent
  let _ := hcomm
  have hcentral : centralizer (B₀ : Set D) = (centralizer (B : Set J)).subgroupOf D := by
    ext x
    constructor
    · intro hx b hb
      exact congrArg Subtype.val (hx ⟨b, hA.inside hb⟩ hb)
    · intro hx b hb
      exact Subtype.ext (hx b hb)
  constructor
  · refine .of_setLike_mul_comm ?_
    intro a ha b hb
    have hac : (⟨a, a.property.2⟩ : D) ∈ centralizer (B₀ : Set D) := hcentral ▸ ha
    have hbc : (⟨b, b.property.2⟩ : D) ∈ centralizer (B₀ : Set D) := hcentral ▸ hb
    exact Subtype.ext (congrArg (fun x : centralizer (B₀ : Set D) => ((x : D) : J))
      (mul_comm' ⟨⟨a, a.property.2⟩, hac⟩ ⟨⟨b, b.property.2⟩, hbc⟩))
  · have hi := two_subgroup_centralizer_index B₀ T₀ hT₀p hT₀n hindex
    change (centralizer (B₀ : Set D)).relIndex T₀ ∣ 2 at hi
    rw [hcentral, relIndex_subgroupOf (show T ≤ D from inf_le_right)] at hi
    exact hi

/-- In the noncyclic unitary case, the centralizer of B in the normalizing
two-subgroup S ∩ D is abelian and has index dividing two. Normalization is
supplied independently; no matrix-centralizer or weight-space premise remains. -/
theorem caseThree_torus_action
    {J : Type*} [Group J] [Finite J]
    {κ : GroupClass} {D B K : Subgroup J} {S : Sylow 2 J} {p q : ℕ}
    [Fact q.Prime] (hA : AmbientInput κ D B S p)
    (hC : CaseThree D B (S : Subgroup J) K q .unitary .unitary)
    (hn : ¬ IsCyclic B) (hlarge : 3 < q)
    (hnorm : (S : Subgroup J) ⊓ D ≤ normalizer B) :
    IsMulCommutative ((centralizer (B : Set J)).subgroupOf ((S : Subgroup J) ⊓ D)) ∧
      ((centralizer (B : Set J)).subgroupOf ((S : Subgroup J) ⊓ D)).index ∣ 2 := by
  apply caseThree_torus_action_of_matrix_centralizers hA hC hn hlarge hnorm
  intro F _ _ R hcomm horder hnR hdet
  let _ : IsMulCommutative R := hcomm
  exact Representation.rankThreeDeterminantCentralizer R horder hnR hdet

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition
