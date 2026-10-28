module

public import Theory.AtlasPort.LinearGroups.G2.ExceptionalLocalQuotients
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The index-nine obstruction for the actual binary derived group

A proper index-nine subgroup of a finite simple perfect group gives a faithful
action in A₉. In the actual derived octonion group, the second parabolic's
two-core contains the already constructed C₄ × C₄. Thus the elementary
nonembedding statement for C₄ × C₄ in A₉ excludes index nine.

The nonembedding statement remains an explicit premise in this reduction.
The subgroup embedding and the faithful coset action are constructed here;
no abstract unitary identification or maximal-subgroup list is used.
Source/application: Aschbacher--Smith, B.1.13, printed p.74 (PDF p.85).
The concrete parabolic embedding is from the licensed ATLAS port cited in
`ExceptionalLocalQuotients`.
-/

public section
namespace Atlas.G2.BinaryNinePointReduction
open Subgroup
open ExceptionalLocalQuotients

private theorem faithful_alternating_action_of_index_nine
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] [Group.IsPerfect G]
    (H : Subgroup G) (hi : H.index = 9) :
    ∃ f : G →* alternatingGroup (Fin 9), Function.Injective f := by
  classical
  have hH : H ≠ ⊤ := by intro h; simp [h] at hi
  have hb : H.normalCore = ⊥ := by
    rcases (inferInstance : H.normalCore.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact False.elim (hH (top_unique (h ▸ H.normalCore_le)))
  let action := MulAction.toPermHom G (G ⧸ H)
  have ha : Function.Injective action := action.ker_eq_bot_iff.mp
    (H.normalCore_eq_ker.symm.trans hb)
  let e : (G ⧸ H) ≃ Fin 9 := (Finite.equivFin _).trans (finCongr hi)
  let f : G →* Equiv.Perm (Fin 9) := (Equiv.permCongrHom e).toMonoidHom.comp action
  have hf : Function.Injective f := (Equiv.permCongrHom e).injective.comp ha
  have heven (g : G) : f g ∈ alternatingGroup (Fin 9) := by
    exact Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp f)
      (Group.IsPerfect.mem_commutator (g := g))
  exact ⟨f.codRestrict _ heven, fun x y h => hf (congrArg Subtype.val h)⟩

/-- The concrete C₄ × C₄ inside the actual derived second parabolic prevents
an index-nine subgroup, once the elementary A₉ obstruction is supplied. -/
theorem index_ne_nine_of_cyclicFourSquare_obstruction
    [IsSimpleGroup (commutator (Model (ZMod 2)))]
    [Group.IsPerfect (commutator (Model (ZMod 2)))]
    (hA : ∀ f : C4Square →* alternatingGroup (Fin 9), ¬ Function.Injective f)
    (H : Subgroup (commutator (Model (ZMod 2)))) : H.index ≠ 9 := by
  intro hi
  obtain ⟨f, hf⟩ := faithful_alternating_action_of_index_nine H hi
  let j : C4Square →* commutator (Model (ZMod 2)) :=
    BinaryParabolicPair.derivedSecond.subtype.comp secondCoreEmbedding
  have hj : Function.Injective j :=
    BinaryParabolicPair.derivedSecond.subtype_injective.comp secondCoreEmbedding_injective
  exact hA (f.comp j) (hf.comp hj)

end Atlas.G2.BinaryNinePointReduction
