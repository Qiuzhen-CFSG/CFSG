module

public import Theory.Alternating.FivePairOuterTwo
public import Theory.GroupTheory.SylowOuterCover

/-!
# Type inertia for a normal A₅ pair

For an actual normal embedding of A₅×A₅, the image, its centralizer, and
any Sylow two-subgroup generate the ambient finite group. In particular,
any module-type inertia subgroup containing all three is the whole group.
This is the same-seed branch of Aschbacher--Smith D.3.9(1), printed p.200:
inner and centralizing operators preserve types, and the original Sylow
subgroup preserves the chosen seed when seed equals its local orbit span.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.AlternatingFive

/-- The literal normally embedded A₅ pair has two-group outer automorphisms. -/
theorem normal_pair_outer_isPGroup_two
    {Q : Type*} [Group Q]
    (i : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →* Q)
    (hi : Function.Injective i) : IsPGroup 2 (MulAut.Outer i.range) := by
  let : IsQuasisimple (alternatingGroup (Fin 5)) := {
    toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let e := MonoidHom.ofInjective hi
  exact (AutomorphismSquare.outer_isPGroup_two
    (alternatingGroup.center_eq_bot (by simp)) outer_isPGroup_two).of_surjective
      (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).surjective

/-- Retain the centralizer in the Sylow cover; no faithfulness premise on it is needed. -/
theorem normal_pair_sup_centralizer_sup_sylow_eq_top
    {Q : Type*} [Group Q] [Finite Q]
    (i : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →* Q)
    (hi : Function.Injective i) [i.range.Normal] (T : Sylow 2 Q) :
    (i.range ⊔ centralizer (i.range : Set Q)) ⊔ (T : Subgroup Q) = ⊤ :=
  sup_centralizer_sup_sylow_eq_top i.range (normal_pair_outer_isPGroup_two i hi) T

/-- The group-theoretic criterion used on the actual local module's type inertia. -/
theorem eq_top_of_normal_pair_centralizer_sylow_le
    {Q : Type*} [Group Q] [Finite Q]
    (i : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →* Q)
    (hi : Function.Injective i) [i.range.Normal] (T : Sylow 2 Q)
    (I : Subgroup Q) (hJ : i.range ≤ I)
    (hC : centralizer (i.range : Set Q) ≤ I) (hT : (T : Subgroup Q) ≤ I) :
    I = ⊤ :=
  eq_top_of_inner_centralizer_sylow_le i.range
    (normal_pair_outer_isPGroup_two i hi) T I hJ hC hT

end Theory.AlternatingFive
