module
public import Theory.GroupTheory.FrattiniFlagQuotientPair
public import Theory.GroupTheory.SylowOuterSectionImages
import all Theory.GroupTheory.FrattiniFlagQuotientPair

/-!
# Simple sections detected on an invariant Frattini flag

The two flag actions have a two-group common kernel. A nonsolvable simple
section of Aut(P) therefore survives on one of the two flag factors.
This keeps actual subgroup surjections, allowing the equal-order groups
PSL₃(4) and GL₄(2) to be distinguished in the source application.

The proof-only import deliberately reuses the internal flag actions and
square-one kernel calculation of FrattiniFlagQuotientPair; their public
boundary is unchanged. Source application: Aschbacher--Smith 4.4.10--11,
printed p.621, via the actual PSU₅(4) Sylow flag.
-/
public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory

/-- A simple section survives on one of two actions with solvable common kernel. -/
theorem simple_section_two_actions
    {A B C S : Type*} [Group A] [Group B] [Group C] [Group S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S) (r : A →* B) (q : A →* C)
    [Group.IsSolvable (r.ker ⊓ q.ker : Subgroup A)]
    (U : Subgroup A) (f : U →* S) (hf : Function.Surjective f) :
    (∃ W : Subgroup B, ∃ g : W →* S, Function.Surjective g) ∨
      ∃ W : Subgroup C, ∃ g : W →* S, Function.Surjective g := by
  rcases simple_section_normal_or_quotient r.ker U f hf with ⟨W,g,hg⟩ | ⟨W,g,hg⟩
  · let k := q.comp r.ker.subtype
    let i : k.ker →* (r.ker ⊓ q.ker : Subgroup A) :=
      { toFun := fun x => ⟨x.val.val,x.val.property,x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hi : Function.Injective i := fun x y he =>
      Subtype.ext (Subtype.ext (congrArg (fun z : (r.ker ⊓ q.ker : Subgroup A) => (z : A)) he))
    let : Group.IsSolvable k.ker := Group.isSolvable_of_isSolvable_injective hi
    exact Or.inr (MulAut.section_image_of_solvable_kernel hS k W g hg)
  · let e := QuotientGroup.quotientKerEquivRange r
    exact Or.inl (MonoidHom.exists_section_of_surjective_of_injective
      (MonoidHom.id (A ⧸ r.ker)) Function.surjective_id
      (r.range.subtype.comp e.toMonoidHom)
      (r.range.subtype_injective.comp e.injective) W g hg)

/-- Actual simple sections of Aut(P) survive on one factor of an invariant Frattini flag. -/
theorem simple_section_invariant_frattini_flag
    {P S : Type*} [Group P] [Finite P] [Group S] [IsSimpleGroup S]
    (hP : IsPGroup 2 P) (hS : ¬ Group.IsSolvable S)
    (Q : Subgroup (P ⧸ frattini P)) [Q.Normal]
    (hQ : ∀ a : MulAut P, Q.map (quotientAut (frattini P) a).toMonoidHom = Q)
    (U : Subgroup (MulAut P)) (f : U →* S) (hf : Function.Surjective f) :
    (∃ W : Subgroup (MulAut Q), ∃ g : W →* S, Function.Surjective g) ∨
      ∃ W : Subgroup (MulAut ((P ⧸ frattini P) ⧸ Q)),
        ∃ g : W →* S, Function.Surjective g := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let ρ := quotientAut (frattini P)
  let r := flagRestriction ρ Q hQ
  let q := flagQuotient ρ Q hQ
  let : Group.IsNilpotent (r.ker ⊓ q.ker : Subgroup (MulAut P)) :=
    (flag_kernel_isPGroup ρ (isPGroup_quotientAut_frattini_kernel hP) Q hQ).isNilpotent
  exact simple_section_two_actions hS r q U f hf

end Theory.GroupTheory
