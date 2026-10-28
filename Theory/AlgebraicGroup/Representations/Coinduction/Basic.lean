module

public import Mathlib.RepresentationTheory.FiniteIndex

universe u v w

namespace Theory.AlgebraicGroup

/-! Finite generation of coinduction from a finite-index subgroup. -/

open scoped MonoidAlgebra
open Representation

public lemma Representation.coind_subtype_moduleFinite
    {k : Type u} {G : Type v} [Field k] [Group G]
    (S : Subgroup G) [S.FiniteIndex]
    (A : Rep.{w} k S) [Module.Finite k A] :
    Module.Finite k (Representation.coindV S.subtype A.ρ) := by
  classical
  let := QuotientGroup.rightRel S
  let Q := Quotient (QuotientGroup.rightRel S)
  let ev : Representation.coindV S.subtype A.ρ →ₗ[k] (Q → A) :=
    { toFun := fun f q => f.1 q.out
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hev : Function.Injective ev := by
    intro f h hfh
    apply Subtype.ext
    funext g
    let q : Q := Quotient.mk' g
    let r : G := q.out
    have hq0 := Quotient.out_eq q
    change (Quotient.mk' r : Q) = q at hq0
    have hq : (Quotient.mk' r : Q) = Quotient.mk' g := hq0
    have hrel : (QuotientGroup.rightRel S) r g := Quotient.eq'.mp hq
    let s : S := ⟨g * r⁻¹, QuotientGroup.rightRel_apply.mp hrel⟩
    have hgr : s.1 * r = g := by simp [s]
    calc
      f.1 g = f.1 (s.1 * r) := by rw [hgr]
      _ = A.ρ s (f.1 r) := f.2 s r
      _ = A.ρ s (h.1 r) := by
        rw [show f.1 r = h.1 r by
          exact congrFun hfh q]
      _ = h.1 (s.1 * r) := (h.2 s r).symm
      _ = h.1 g := by rw [hgr]
  let : Finite Q :=
    Finite.of_equiv (G ⧸ S) (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm
  let : Fintype Q := Fintype.ofFinite Q
  let : Module.Finite k (Q → A) := Module.Finite.pi
  exact Module.Finite.of_injective ev hev

/-! Finite generation of induction from a finite-index subgroup. -/

public lemma Representation.ind_subtype_moduleFinite
    {k : Type u} {G : Type v} [Field k] [Group G]
    (S : Subgroup G) [S.FiniteIndex]
    (A : Rep.{max w u} k S) [Module.Finite k A] :
    Module.Finite k (Rep.ind S.subtype A) := by
  classical
  let : Module.Finite k (Rep.coind S.subtype A) :=
    Representation.coind_subtype_moduleFinite S A
  apply Module.Finite.of_injective (Rep.indToCoind A)
  intro x y hxy
  have h := congrArg (fun z => Rep.coindToInd A z) hxy
  have hcomp := Rep.indToCoind_coindToInd A
  simpa only [← LinearMap.comp_apply, hcomp, LinearMap.id_apply] using h

end Theory.AlgebraicGroup
