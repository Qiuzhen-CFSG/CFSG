module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Finite certificates for the six-point action of S₅

The six labels are the nonidentity elements in the six cyclic subgroups of
order five. Conjugation by transpositions permutes these labels. All displayed
permutation identities are checked in the kernel, using direct point tables.
The normalizer table lists the twenty possible permutations intertwining a
fixed five-cycle with one of its four generators.

These are the finite certificates for the actual M₁₂ 2A centralizer embedding
used in Aschbacher–Smith, Lemma 16.1.5(4), printed p.1171. The source generator
in `source/generate.py` produces candidate tables only; Lean checks the identities.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12Centralizer2A
set_option maxRecDepth 10000

def cycleTable : Fin 24 → Fin 5 → Fin 5 := ![![1, 4, 3, 0, 2], ![4, 2, 0, 1, 3], ![2, 3, 1, 4, 0], ![3, 0, 4, 2, 1], ![1, 3, 0, 4, 2], ![3, 4, 1, 2, 0], ![4, 2, 3, 0, 1], ![2, 0, 4, 1, 3], ![1, 2, 4, 0, 3], ![2, 4, 3, 1, 0], ![4, 3, 0, 2, 1], ![3, 0, 1, 4, 2], ![1, 2, 3, 4, 0], ![2, 3, 4, 0, 1], ![3, 4, 0, 1, 2], ![4, 0, 1, 2, 3], ![1, 3, 4, 2, 0], ![3, 2, 0, 4, 1], ![2, 4, 1, 0, 3], ![4, 0, 3, 1, 2], ![1, 4, 0, 2, 3], ![4, 3, 1, 0, 2], ![3, 2, 4, 1, 0], ![2, 0, 3, 4, 1]]
def inverseTable : Fin 24 → Fin 5 → Fin 5 := ![![3, 0, 4, 2, 1], ![2, 3, 1, 4, 0], ![4, 2, 0, 1, 3], ![1, 4, 3, 0, 2], ![2, 0, 4, 1, 3], ![4, 2, 3, 0, 1], ![3, 4, 1, 2, 0], ![1, 3, 0, 4, 2], ![3, 0, 1, 4, 2], ![4, 3, 0, 2, 1], ![2, 4, 3, 1, 0], ![1, 2, 4, 0, 3], ![4, 0, 1, 2, 3], ![3, 4, 0, 1, 2], ![2, 3, 4, 0, 1], ![1, 2, 3, 4, 0], ![4, 0, 3, 1, 2], ![2, 4, 1, 0, 3], ![3, 2, 0, 4, 1], ![1, 3, 4, 2, 0], ![2, 0, 3, 4, 1], ![3, 2, 4, 1, 0], ![4, 3, 1, 0, 2], ![1, 4, 0, 2, 3]]
def cycle (i : Fin 24) : Equiv.Perm (Fin 5) where
  toFun := cycleTable i
  invFun := inverseTable i
  left_inv := (by decide +kernel : ∀ i x, inverseTable i (cycleTable i x) = x) i
  right_inv := (by decide +kernel : ∀ i x, cycleTable i (inverseTable i x) = x) i

def label (i : Fin 6) : Finset (Equiv.Perm (Fin 5)) :=
  Finset.univ.image (fun j : Fin 4 => cycle ⟨4*i.val+j.val, by omega⟩)
def conjugate (s : Equiv.Perm (Fin 5)) (L : Finset (Equiv.Perm (Fin 5))) :=
  L.image (fun c => s * c * s⁻¹)
theorem label_injective : Function.Injective label := by decide +kernel
def swapIndex : Fin 5 → Fin 5 → Fin 6 → Fin 6 := ![![![0, 1, 2, 3, 4, 5], ![4, 2, 1, 5, 0, 3], ![1, 0, 3, 2, 5, 4], ![3, 4, 5, 0, 1, 2], ![5, 3, 4, 1, 2, 0]], ![![4, 2, 1, 5, 0, 3], ![0, 1, 2, 3, 4, 5], ![3, 5, 4, 0, 2, 1], ![2, 3, 0, 1, 5, 4], ![1, 0, 5, 4, 3, 2]], ![![1, 0, 3, 2, 5, 4], ![3, 5, 4, 0, 2, 1], ![0, 1, 2, 3, 4, 5], ![5, 2, 1, 4, 3, 0], ![2, 4, 0, 5, 1, 3]], ![![3, 4, 5, 0, 1, 2], ![2, 3, 0, 1, 5, 4], ![5, 2, 1, 4, 3, 0], ![0, 1, 2, 3, 4, 5], ![4, 5, 3, 2, 0, 1]], ![![5, 3, 4, 1, 2, 0], ![1, 0, 5, 4, 3, 2], ![2, 4, 0, 5, 1, 3], ![4, 5, 3, 2, 0, 1], ![0, 1, 2, 3, 4, 5]]]

def powerIndex : Fin 5 → Fin 5 → Fin 6 → Fin 4 → Fin 4 := ![![![![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]], ![![3, 2, 1, 0], ![3, 2, 1, 0], ![3, 2, 1, 0], ![3, 2, 1, 0], ![3, 2, 1, 0], ![3, 2, 1, 0]], ![![1, 3, 0, 2], ![2, 0, 3, 1], ![3, 2, 1, 0], ![3, 2, 1, 0], ![1, 3, 0, 2], ![2, 0, 3, 1]], ![![2, 0, 3, 1], ![3, 2, 1, 0], ![2, 0, 3, 1], ![1, 3, 0, 2], ![3, 2, 1, 0], ![1, 3, 0, 2]], ![![3, 2, 1, 0], ![1, 3, 0, 2], ![1, 3, 0, 2], ![2, 0, 3, 1], ![2, 0, 3, 1], ![3, 2, 1, 0]]], ![![![3, 2, 1, 0], ![3, 2, 1, 0], ![3, 2, 1, 0], ![3, 2, 1, 0], ![3, 2, 1, 0], ![3, 2, 1, 0]], ![![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]], ![![1, 3, 0, 2], ![3, 2, 1, 0], ![2, 0, 3, 1], ![2, 0, 3, 1], ![1, 3, 0, 2], ![3, 2, 1, 0]], ![![3, 2, 1, 0], ![2, 0, 3, 1], ![3, 2, 1, 0], ![1, 3, 0, 2], ![2, 0, 3, 1], ![1, 3, 0, 2]], ![![2, 0, 3, 1], ![1, 3, 0, 2], ![1, 3, 0, 2], ![3, 2, 1, 0], ![3, 2, 1, 0], ![2, 0, 3, 1]]], ![![![1, 3, 0, 2], ![2, 0, 3, 1], ![3, 2, 1, 0], ![3, 2, 1, 0], ![1, 3, 0, 2], ![2, 0, 3, 1]], ![![1, 3, 0, 2], ![3, 2, 1, 0], ![2, 0, 3, 1], ![2, 0, 3, 1], ![1, 3, 0, 2], ![3, 2, 1, 0]], ![![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]], ![![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]], ![![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]], ![![![2, 0, 3, 1], ![3, 2, 1, 0], ![2, 0, 3, 1], ![1, 3, 0, 2], ![3, 2, 1, 0], ![1, 3, 0, 2]], ![![3, 2, 1, 0], ![2, 0, 3, 1], ![3, 2, 1, 0], ![1, 3, 0, 2], ![2, 0, 3, 1], ![1, 3, 0, 2]], ![![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]], ![![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]], ![![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]], ![![![3, 2, 1, 0], ![1, 3, 0, 2], ![1, 3, 0, 2], ![2, 0, 3, 1], ![2, 0, 3, 1], ![3, 2, 1, 0]], ![![2, 0, 3, 1], ![1, 3, 0, 2], ![1, 3, 0, 2], ![3, 2, 1, 0], ![3, 2, 1, 0], ![2, 0, 3, 1]], ![![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]], ![![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]], ![![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3], ![0, 1, 2, 3]]]]
theorem swap_cycle : ∀ a b : Fin 5, ∀ i : Fin 6, ∀ j : Fin 4,
    Equiv.swap a b * cycle ⟨4*i.val+j.val, by omega⟩ * (Equiv.swap a b)⁻¹ =
      cycle ⟨4*(swapIndex a b i).val+(powerIndex a b i j).val, by omega⟩ := by
  decide +kernel

def normalizerTable : Fin 5 → Fin 4 → Fin 5 → Fin 5 := ![![![0, 1, 2, 3, 4], ![0, 4, 1, 2, 3], ![0, 2, 3, 4, 1], ![0, 3, 4, 1, 2]], ![![1, 4, 3, 0, 2], ![1, 2, 4, 3, 0], ![1, 3, 0, 2, 4], ![1, 0, 2, 4, 3]], ![![2, 3, 1, 4, 0], ![2, 0, 3, 1, 4], ![2, 1, 4, 0, 3], ![2, 4, 0, 3, 1]], ![![3, 0, 4, 2, 1], ![3, 1, 0, 4, 2], ![3, 4, 2, 1, 0], ![3, 2, 1, 0, 4]], ![![4, 2, 0, 1, 3], ![4, 3, 2, 0, 1], ![4, 0, 1, 3, 2], ![4, 1, 3, 2, 0]]]
def normalizerInverse : Fin 5 → Fin 4 → Fin 5 → Fin 5 := ![![![0, 1, 2, 3, 4], ![0, 2, 3, 4, 1], ![0, 4, 1, 2, 3], ![0, 3, 4, 1, 2]], ![![3, 0, 4, 2, 1], ![4, 0, 1, 3, 2], ![2, 0, 3, 1, 4], ![1, 0, 2, 4, 3]], ![![4, 2, 0, 1, 3], ![1, 3, 0, 2, 4], ![3, 1, 0, 4, 2], ![2, 4, 0, 3, 1]], ![![1, 4, 3, 0, 2], ![2, 1, 4, 0, 3], ![4, 3, 2, 0, 1], ![3, 2, 1, 0, 4]], ![![2, 3, 1, 4, 0], ![3, 4, 2, 1, 0], ![1, 2, 4, 3, 0], ![4, 1, 3, 2, 0]]]
def normalizerPerm (x : Fin 5) (j : Fin 4) : Equiv.Perm (Fin 5) where
  toFun := normalizerTable x j
  invFun := normalizerInverse x j
  left_inv := (by decide +kernel : ∀ x j i, normalizerInverse x j (normalizerTable x j i) = i) x j
  right_inv := (by decide +kernel : ∀ x j i, normalizerTable x j (normalizerInverse x j i) = i) x j

theorem normalizer_semiconj_eq : ∀ (x : Fin 5) (j : Fin 4),
    normalizerPerm x j * cycle 0 = cycle ⟨j.val, by omega⟩ * normalizerPerm x j := by
  decide +kernel

theorem normalizer_zero : ∀ x j, normalizerPerm x j 0 = x := by decide +kernel

end Sporadic.Mathieu.M12Centralizer2A
