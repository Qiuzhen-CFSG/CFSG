module

public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.Morphism.Operations

universe u

/-!
Zariski closures of abstract subgroups of algebraic-group points.

Besides constructing the closed subgroup, this module compares commutators
before and after closure.  Continuity of the commutator morphisms gives one
containment, while monotonicity of abstract commutators gives the reverse
containment after taking closure.  The resulting equality is the general
closure step used when a root-generated subgroup is identified with the
derived subgroup of an algebraic subgroup, as in the standard Levi
calculation of GLS3, Theorem 1.13.3(d).
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- The Zariski closure of an abstract subgroup, packaged as a closed
algebraic subgroup. -/
@[expose]
public noncomputable def subgroupZariskiClosure
    (G : Variety k) [AlgebraicGroup G]
    (H : Subgroup (Variety.Point G)) : ClosedSubgroup G :=
  let K : Subgroup (Variety.Point G) :=
    { carrier := closure (H : Set (Variety.Point G))
      one_mem' := subset_closure H.one_mem
      mul_mem' := by
        intro x y hx hy
        exact map_mem_closure₂'
          (fun x ↦ (AlgebraicGroup.leftMulMorphism G x).continuous)
          (fun y ↦ (AlgebraicGroup.rightMulMorphism G y).continuous)
          hx hy (fun a ha b hb ↦ H.mul_mem ha hb)
      inv_mem' := by
        intro x hx
        apply map_mem_closure (AlgebraicGroup.invMorphism G).continuous hx
        intro z hz
        exact H.inv_mem hz }
  ClosedSubgroup.ofSubgroup K
    (Variety.isClosed_iff_isZariskiClosed.mp isClosed_closure)

open scoped commutatorElement

private lemma commutator_subgroupZariskiClosure_le_two_aux
    (G : Variety k) [AlgebraicGroup G]
    (H K : Subgroup (Variety.Point G)) :
    ⁅(subgroupZariskiClosure G H).toSubgroup,
        (subgroupZariskiClosure G K).toSubgroup⁆ ≤
      (subgroupZariskiClosure G ⁅H, K⁆).toSubgroup := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  change ⁅x, y⁆ ∈ closure (⁅H, K⁆ : Subgroup (Variety.Point G))
  have hcontinuousLeft : Continuous (fun z : Variety.Point G ↦ ⁅z, y⁆) := by
    let f : Variety.Morphism G G :=
      (AlgebraicGroup.rightMulMorphism G y⁻¹).comp
        (AlgebraicGroup.conjugateMorphism G y)
    have hf : (fun z : Variety.Point G ↦ ⁅z, y⁆) = f.toFun := by
      funext z
      simp [f, Variety.Morphism.comp,
        AlgebraicGroup.rightMulMorphism_apply,
        AlgebraicGroup.conjugateMorphism_apply,
        commutatorElement_def, mul_assoc]
    rw [hf]
    exact f.continuous
  refine (Set.MapsTo.closure_left ?_ hcontinuousLeft isClosed_closure) hx
  intro a ha
  have hcontinuousRight : Continuous (fun z : Variety.Point G ↦ ⁅a, z⁆) := by
    let f : Variety.Morphism G G :=
      (AlgebraicGroup.leftMulMorphism G a).comp
        (AlgebraicGroup.conjugateMorphism G a⁻¹)
    have hf : (fun z : Variety.Point G ↦ ⁅a, z⁆) = f.toFun := by
      funext z
      simp [f, Variety.Morphism.comp,
        AlgebraicGroup.leftMulMorphism_apply,
        AlgebraicGroup.conjugateMorphism_apply,
        commutatorElement_def, mul_assoc]
    rw [hf]
    exact f.continuous
  apply map_mem_closure hcontinuousRight hy
  intro b hb
  exact Subgroup.commutator_mem_commutator ha hb

/-- The commutator subgroup of one Zariski closure lies in the Zariski
closure of the abstract commutator subgroup. -/
public lemma commutator_subgroupZariskiClosure_le
    (G : Variety k) [AlgebraicGroup G]
    (H : Subgroup (Variety.Point G)) :
    ⁅(subgroupZariskiClosure G H).toSubgroup,
        (subgroupZariskiClosure G H).toSubgroup⁆ ≤
      (subgroupZariskiClosure G ⁅H, H⁆).toSubgroup :=
  commutator_subgroupZariskiClosure_le_two_aux G H H

/-- Taking the Zariski closure after forming a commutator gives the same
closed subgroup whether or not the original subgroup is closed first. -/
public lemma subgroupZariskiClosure_commutator_closure_eq
    (G : Variety k) [AlgebraicGroup G]
    (H : Subgroup (Variety.Point G)) :
    subgroupZariskiClosure G
        ⁅(subgroupZariskiClosure G H).toSubgroup,
          (subgroupZariskiClosure G H).toSubgroup⁆ =
      subgroupZariskiClosure G ⁅H, H⁆ := by
  let A : Subgroup (Variety.Point G) :=
    ⁅(subgroupZariskiClosure G H).toSubgroup,
      (subgroupZariskiClosure G H).toSubgroup⁆
  let B : Subgroup (Variety.Point G) := ⁅H, H⁆
  have hAB : A ≤ (subgroupZariskiClosure G B).toSubgroup := by
    dsimp only [A, B]
    exact commutator_subgroupZariskiClosure_le G H
  have hBA : B ≤ A := by
    dsimp only [A, B]
    apply Subgroup.commutator_mono
    · intro y hy
      exact subset_closure hy
    · intro y hy
      exact subset_closure hy
  apply SetLike.ext
  intro x
  change x ∈ closure (A : Set (Variety.Point G)) ↔
    x ∈ closure (B : Set (Variety.Point G))
  constructor
  · intro hx
    exact closure_minimal hAB isClosed_closure hx
  · intro hx
    exact closure_mono hBA hx

/-- Mixed commutators of two Zariski closures lie in the Zariski closure of
the corresponding abstract mixed commutator subgroup. -/
public lemma commutator_subgroupZariskiClosure_le_two
    (G : Variety k) [AlgebraicGroup G]
    (H K : Subgroup (Variety.Point G)) :
    ⁅(subgroupZariskiClosure G H).toSubgroup,
        (subgroupZariskiClosure G K).toSubgroup⁆ ≤
      (subgroupZariskiClosure G ⁅H, K⁆).toSubgroup :=
  commutator_subgroupZariskiClosure_le_two_aux G H K

/-- The Zariski closure of a normal abstract subgroup is normal. -/
public lemma subgroupZariskiClosure_isNormal
    (G : Variety k) [AlgebraicGroup G]
    (H : Subgroup (Variety.Point G)) (hH : H.Normal) :
    (subgroupZariskiClosure G H).toSubgroup.Normal := by
  refine ⟨?_⟩
  intro n hn g
  change g * n * g⁻¹ ∈ closure (H : Set (Variety.Point G))
  apply map_mem_closure
    (AlgebraicGroup.conjugationByMorphism G g).continuous hn
  intro m hm
  rw [AlgebraicGroup.conjugationByMorphism_apply]
  exact hH.conj_mem m hm g

/-- The Zariski closure of a cyclic subgroup is abelian. -/
public lemma subgroupZariskiClosure_zpowers_isAbelian
    {G : Variety k} [AlgebraicGroup G] (x : Variety.Point G) :
    ∀ a b,
      a ∈ (subgroupZariskiClosure G (Subgroup.zpowers x)).toSubgroup →
      b ∈ (subgroupZariskiClosure G (Subgroup.zpowers x)).toSubgroup →
      a * b = b * a := by
  intro a b ha hb
  have hzcomm (z : Variety.Point G) (hz : z ∈ Subgroup.zpowers x) :
      z * b = b * z := by
    let C : Set (Variety.Point G) := {y | z * y = y * z}
    have hCclosed : IsClosed C := by
      apply Variety.isClosed_iff_isZariskiClosed.mpr
      simpa [C, AlgebraicGroup.leftMulMorphism_apply,
        AlgebraicGroup.rightMulMorphism_apply] using
        Variety.Morphism.isZariskiClosed_equalizer
          (AlgebraicGroup.leftMulMorphism G z)
          (AlgebraicGroup.rightMulMorphism G z)
    have hsub : (Subgroup.zpowers x : Set (Variety.Point G)) ⊆ C := by
      intro y hy
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨m, rfl⟩
      rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
      exact (Commute.refl x).zpow_zpow m n
    exact closure_minimal hsub hCclosed hb
  let D : Set (Variety.Point G) := {y | y * b = b * y}
  have hDclosed : IsClosed D := by
    apply Variety.isClosed_iff_isZariskiClosed.mpr
    simpa [D, AlgebraicGroup.leftMulMorphism_apply,
      AlgebraicGroup.rightMulMorphism_apply] using
      Variety.Morphism.isZariskiClosed_equalizer
        (AlgebraicGroup.rightMulMorphism G b)
        (AlgebraicGroup.leftMulMorphism G b)
  have hsubD : (Subgroup.zpowers x : Set (Variety.Point G)) ⊆ D := by
    intro z hz
    exact hzcomm z hz
  exact closure_minimal hsubD hDclosed ha

end Theory.AlgebraicGroup
