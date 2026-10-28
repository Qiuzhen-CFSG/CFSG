module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalResidualCard
public import Mathlib.GroupTheory.Perm.Finite

/-!
# The literal four-letter alternating subgroup

The canonical subgroup K acts on the first four letters and fixes the last
two. The sum embedding of A₄ has image K: its image lies in K, and the
natural point-residual order calculation gives both groups order twelve.
This supplies the actual A₄ quotient marking used in 13.7.10(8), rather
than treating the phrase "embedded A₄" as an unproved equivalence.
Source: Aschbacher–Smith, §B.3 and 13.7.10(8), printed pp.83–85 and 942.
-/

@[expose] public section
open Subgroup Equiv
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags
open BinaryPermutation NaturalGeometry NaturalPairing Representation.BinaryOffender

theorem card_K : Nat.card K=12 := by
  have hh := NaturalResidualCard.point_residual_card (⊤:Subgroup S) le_top
    canonicalLine canonicalLine_finrank
  have he : (⊤⊓subspaceStabilizer (naturalRepresentation (Fin 6)) canonicalLine:Subgroup S)=H1 := by
    ext g
    simp only [mem_inf,mem_top,true_and,mem_stabilizer_iff_map,canonicalLine_stabilizer]
  dsimp only at hh
  rw [he,residual_H1] at hh
  exact hh

def fourLetterHom : alternatingGroup (Fin 4) →* S :=
  (Equiv.permCongrHom (finSumFinEquiv:Fin 4⊕Fin 2≃Fin 6)).toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom _ _).comp
      ((alternatingGroup (Fin 4)).subtype.prod (1:alternatingGroup (Fin 4)→*Equiv.Perm (Fin 2))))

theorem fourLetterHom_injective : Function.Injective fourLetterHom := by
  intro a b h
  have hh := Equiv.Perm.sumCongrHom_injective ((Equiv.permCongrHom _).injective h)
  exact Subtype.ext (congrArg Prod.fst hh)

theorem fourLetterHom_range : fourLetterHom.range=K := by
  have hle : fourLetterHom.range≤K := by
    rintro _ ⟨a,rfl⟩
    let : Fintype (Equiv.Perm (Fin 4)) := inferInstance
    exact (show ∀a:alternatingGroup (Fin 4),fourLetterHom a∈K by decide +kernel) a
  apply eq_of_le_of_card_ge hle
  rw [card_K,←Nat.card_congr (MonoidHom.ofInjective fourLetterHom_injective).toEquiv,
    Nat.card_eq_fintype_card,card_alternatingGroup]
  norm_num [Nat.factorial]

noncomputable def fourLetterEquiv : K≃*alternatingGroup (Fin 4) :=
  (MulEquiv.subgroupCongr fourLetterHom_range.symm).trans
    (MonoidHom.ofInjective fourLetterHom_injective).symm
end Theory.SpecificGroups.SymmetricSix.BinaryFlags
