module

public import Theory.Representation.CommutingCentralizersCohomology
public import Theory.Representation.BinaryAlternatingSevenFixedPoints
public import Theory.SpecificGroups.AlternatingSevenCentralizerGeneration
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# Four-dimensional binary representations of A₇ and first cohomology

An irreducible four-dimensional representation of A₇ is faithful: simplicity
reduces the contrary case to a trivial action, which preserves every line.
Two commuting three-cycles whose centralizers generate A₇ then suffice to kill
first cohomology, since three-cycles act without fixed vectors.

The final theorem combines the permutation-generation and fixed-point results
for an arbitrary irreducible representation, covering every isomorphism class.
The fixed-point proof uses the Klein four subgroup centralizing a three-cycle:
it cannot act faithfully in the matrix centralizer of a nonidentity cubic
operator with a fixed plane. The conditional assembly criterion remains
available separately.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(8), printed p.408/PDF p.419, citing Exercise 6.3 of [Asc86a].
-/

@[expose] public section

namespace Representation

/-- Every four-dimensional irreducible binary A₇-representation is faithful. -/
theorem binaryAlternatingSeven_faithful_of_irreducible_four
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    [IsIrreducible ρ] (hdim : Module.finrank (ZMod 2) V = 4) :
    Function.Injective ρ := by
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top
    (by norm_num : 5 ≤ Nat.card (Fin 7)) (N := ρ.ker) with hker | hker
  · exact ρ.ker_eq_bot_iff.mp hker
  have htriv (g : alternatingGroup (Fin 7)) : ρ g = 1 := by
    exact show g ∈ ρ.ker from hker ▸ Subgroup.mem_top g
  let b := Module.finBasisOfFinrankEq (ZMod 2) V hdim
  let W : Subrepresentation ρ :=
    { toSubmodule := Submodule.span (ZMod 2) {b 0}
      apply_mem_toSubmodule := by
        intro g v hv
        simpa only [htriv, Module.End.one_apply] using hv }
  have hWne : W ≠ ⊥ := by
    intro hW
    have hv : b 0 ∈ W := Submodule.subset_span (Set.mem_singleton (b 0))
    rw [hW] at hv
    exact b.ne_zero 0 hv
  have hWtop : W = ⊤ :=
    (eq_bot_or_eq_top W).resolve_left hWne
  have he : W.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule hWtop
  have hd : Module.finrank (ZMod 2) W.toSubmodule = 1 :=
    finrank_span_singleton (b.ne_zero 0)
  rw [he, finrank_top, hdim] at hd
  contradiction

/-- Assembly of the two centralizer inputs, with no choice of a module model.
The unconditional four-dimensional result below supplies both inputs. -/
theorem binaryAlternatingSeven_finrank_H1_eq_zero_of_threeCycle_data
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    (hfixed : ∀ a : alternatingGroup (Fin 7),
      Equiv.Perm.IsThreeCycle (a : Equiv.Perm (Fin 7)) →
      ∀ v : V, ρ a v = v → v = 0)
    (hgenerators : ∃ a b : alternatingGroup (Fin 7),
      Equiv.Perm.IsThreeCycle (a : Equiv.Perm (Fin 7)) ∧
      Equiv.Perm.IsThreeCycle (b : Equiv.Perm (Fin 7)) ∧ Commute a b ∧
      Subgroup.centralizer ({a} : Set (alternatingGroup (Fin 7))) ⊔
        Subgroup.centralizer ({b} : Set (alternatingGroup (Fin 7))) = ⊤) :
    Module.finrank (ZMod 2) (OneCohomology.H1 ρ) = 0 := by
  obtain ⟨a, b, ha, hb, hab, hgen⟩ := hgenerators
  let := OneCohomology.subsingleton_H1_of_commuting_centralizers ρ a b hab
    (hfixed a ha) (hfixed b hb) hgen
  exact Module.finrank_zero_of_subsingleton

/-- Every four-dimensional irreducible binary representation of A₇ has zero
first cohomology, as in Aschbacher--Smith Lemma I.1.6(8). No choice of a module
model or additional centralizer hypothesis is needed. -/
theorem binaryAlternatingSeven_finrank_H1_eq_zero_of_irreducible_four
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    [IsIrreducible ρ] (hdim : Module.finrank (ZMod 2) V = 4) :
    Module.finrank (ZMod 2) (OneCohomology.H1 ρ) = 0 :=
  binaryAlternatingSeven_finrank_H1_eq_zero_of_threeCycle_data ρ
    (binaryAlternatingSeven_threeCycle_fixedPointFree ρ
      (binaryAlternatingSeven_faithful_of_irreducible_four ρ hdim) hdim)
    alternatingGroup.exists_commuting_threeCycles_centralizer_sup_eq_top_seven

end Representation
