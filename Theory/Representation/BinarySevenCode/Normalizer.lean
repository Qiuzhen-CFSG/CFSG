module

public import Theory.Representation.BinarySevenCode.PermutationAction
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Simplex centralizers in a seven-point normalizer action

A marking of the actual conjugation action of N(V) by permutations of seven
coordinates transports the binary simplex code into V. Its pointwise fixer
inside N(V) is exactly C(V), because simplex words distinguish coordinates.
This is a local calculation: it does not assert that the ambient centralizer
of the simplex subgroup lies in N(V).

The application is the missing simplex branch in Aschbacher--Smith,
Lemma 12.3.9, printed p.810. The code and its coordinate-separation theorem
are in `BinarySevenCode`; no classification of ambient groups is used here.
-/

@[expose] public section
namespace BinarySevenCode
open Subgroup
variable {G : Type*} [Group G]

/-- A marking of the whole normalizer action, including its literal
conjugation map. The permutation homomorphism need not be injective. -/
structure NormalizerModel (V : Subgroup G) where
  coordinates : V ≃* Multiplicative EvenWord
  permutation : normalizer (V : Set G) →* Equiv.Perm (Fin 7)
  equivariant : ∀ (n : normalizer (V : Set G)) (v : V),
    (coordinates (V.normalizerMonoidHom n v)).toAdd =
      evenRepresentation (permutation n) (coordinates v).toAdd

namespace NormalizerModel
variable {V : Subgroup G} (D : NormalizerModel V)

/-- The actual subgroup of V corresponding to the displayed simplex code. -/
def simplex : Subgroup G :=
  (((simplexCode.comap evenWords.subtype).toAddSubgroup.toSubgroup).comap
    D.coordinates.toMonoidHom).map V.subtype

theorem simplex_le : D.simplex ≤ V := map_subtype_le _

theorem mem_simplex (v : V) :
    (v : G) ∈ D.simplex ↔ (D.coordinates v).toAdd.val ∈ simplexCode := by
  constructor
  · rintro ⟨w, hw, he⟩
    have : w = v := Subtype.ext he
    subst w
    exact hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem simplex_ne_bot : D.simplex ≠ ⊥ := by
  let w : EvenWord := ⟨encode ![1, 0, 0], encode_mem_evenWords _⟩
  let v : V := D.coordinates.symm (Multiplicative.ofAdd w)
  have hv : (v : G) ∈ D.simplex := by
    apply (D.mem_simplex v).mpr
    simp only [v, D.coordinates.apply_symm_apply, toAdd_ofAdd]
    exact (mem_simplexCode_iff _).mpr ⟨![1, 0, 0], rfl⟩
  intro hb
  have hv1 : v = 1 := Subtype.ext (mem_bot.mp (hb ▸ hv))
  have hw : w = 0 := by
    have he := congrArg D.coordinates hv1
    exact congrArg Multiplicative.toAdd
      (show Multiplicative.ofAdd w = 1 by
        simpa only [v, D.coordinates.apply_symm_apply, map_one] using he)
  exact one_ne_zero (congrArg (fun x : EvenWord => x.val 1) hw)

/-- An element normalizing V and fixing its simplex subgroup acts trivially
on all seven coordinates. -/
theorem permutation_eq_one_of_centralizes_simplex
    (n : normalizer (V : Set G)) (hn : (n : G) ∈ centralizer (D.simplex : Set G)) :
    D.permutation n = 1 := by
  apply perm_eq_one_of_fixes_simplexCode
  intro w hw i
  let w' : EvenWord := ⟨w, simplexCode_le_evenWords hw⟩
  let v : V := D.coordinates.symm (Multiplicative.ofAdd w')
  have hv : (v : G) ∈ D.simplex := by
    apply (D.mem_simplex v).mpr
    simpa only [v, D.coordinates.apply_symm_apply, toAdd_ofAdd] using hw
  have hfix : V.normalizerMonoidHom n v = v := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hn) _ hv).symm
  have he := D.equivariant n v
  rw [hfix] at he
  simp only [v, D.coordinates.apply_symm_apply, toAdd_ofAdd] at he
  have hi := congrArg (fun x : EvenWord => x.val (D.permutation n i)) he
  simpa only [evenRepresentation_apply, Equiv.symm_apply_apply] using hi

/-- The local simplex centralizer is the full module centralizer. -/
theorem normalizer_inf_simplex_centralizer :
    normalizer (V : Set G) ⊓ centralizer (D.simplex : Set G) =
      centralizer (V : Set G) := by
  apply le_antisymm
  · intro n hn
    let n' : normalizer (V : Set G) := ⟨n, hn.1⟩
    have hp := D.permutation_eq_one_of_centralizes_simplex n' hn.2
    apply mem_centralizer_iff.mpr
    intro v hv
    have he := D.equivariant n' ⟨v, hv⟩
    rw [hp, map_one] at he
    have hfix : V.normalizerMonoidHom n' ⟨v, hv⟩ = ⟨v, hv⟩ :=
      D.coordinates.injective (Multiplicative.toAdd.injective he)
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hfix)).symm
  · exact le_inf (centralizer_le_normalizer _) (centralizer_le D.simplex_le)

end NormalizerModel
end BinarySevenCode
