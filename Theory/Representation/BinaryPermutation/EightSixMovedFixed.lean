module
public import Theory.Representation.BinaryPermutation.CoreFixedLine
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.Representation.BinaryOffender.NormalizerConjugateDimension
public import Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.Orbits

/-!
# Fixed vectors in local moved spaces of the binary eight-letter modules

The natural six-space has no nonzero A8-fixed vector. In the augmentation
core, A8-fixed vectors are constant, while every A6 commutator vanishes
on the two letters fixed by that A6. Their intersection is therefore zero.
This uses the actual permutation action, with an arbitrary A6 embedding.

Source application: Aschbacher--Smith, 12.6.17, printed p.827: the local
fixed line inside the original moved five-space is moved by the A8 actor.
-/

public section
namespace BinaryPermutation
open Subgroup Representation Representation.BinaryOffender

theorem eight_natural_fixed_eq_zero (v : natural (Fin 8))
    (hv : ∀ g : alternatingGroup (Fin 8), alternatingNaturalRepresentation (Fin 8) g v = v) :
    v = 0 := by
  have hf : Function.Injective (alternatingNaturalRepresentation (Fin 8)) := by
    intro g h he
    exact Subtype.ext (naturalRepresentation_injective (Fin 8) (by decide) he)
  exact (invariants_eq_bot_of_faithful_irreducible _ hf
    (alternatingNatural_isIrreducible (by decide : 5 ≤ Fintype.card (Fin 8)))).le hv

theorem eight_core_six_moved_fixed_eq_zero
    (A : Subgroup (alternatingGroup (Fin 8))) (e : A ≃* alternatingGroup (Fin 6))
    (v : core (Fin 8))
    (hv : v ∈ subspaceCommutator (alternatingCoreRepresentation (Fin 8)) ⊤ A)
    (hf : ∀ g : alternatingGroup (Fin 8), alternatingCoreRepresentation (Fin 8) g v = v) :
    v = 0 := by
  let f := (alternatingGroup (Fin 8)).subtype.comp (A.subtype.comp e.symm.toMonoidHom)
  obtain ⟨i,j,hij,hfix⟩ :=
    Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.exists_fixed_pair f
  let ev : core (Fin 8) →ₗ[ZMod 2] ZMod 2 :=
    (LinearMap.proj i).comp (core (Fin 8)).subtype
  have hz : subspaceCommutator (alternatingCoreRepresentation (Fin 8)) ⊤ A ≤ ev.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,w,_,rfl⟩
    change w.val (g.val.symm i) - w.val i = 0
    have hi : g.val i = i := by
      have hh := (hfix (e ⟨g,hg⟩)).1
      change (e.symm (e ⟨g,hg⟩)).val.val i = i at hh
      simpa only [e.symm_apply_apply] using hh
    rw [g.val.symm_apply_eq.mpr hi.symm,sub_self]
  obtain ⟨c,hc⟩ := (mem_constants_iff v.val).mp
    ((core_fixed_iff_constant (by simp : 3 ≤ Nat.card (Fin 8)) v).mp hf)
  have hvi : v.val i = 0 := hz hv
  apply Subtype.ext
  funext k
  exact (hc k).trans ((hc i).symm.trans hvi)
end BinaryPermutation
