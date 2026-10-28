module
public import Theory.Mathieu.M22.ChapterHLocalClassification.Sylow.Candidates

/-!
# Small centralizer certificates in the marked M22 Sylow

Four displayed elements of each inner E16 suffice to test its centralizer.
For all 1024 ambient rows, pair preservation and commutation on three
separating coordinates force membership in the octad pointwise kernel or
in the 64-element sextet translation list, respectively. The implication
checks are small; no multiplication table or elementary-subgroup search
is trusted. The subsequent module applies them to actual native elements.

Source: Aschbacher--Smith H.14.3(1), printed p.397. The indices refer to
the previously certified native enumeration, with the corrected source
conjugator in Marking. The entire finite check is kernel verified.
-/

@[expose] public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
namespace Sporadic.Mathieu.M22ChapterH.CompatibleSylow

def basisIndex : Fin 2 → Fin 4 → Fin 1024 :=
  ![![14,16,27,38], ![2,3,8,104]]

def testPoint : Fin 3 → Fin 24 := ![9,12,18]

theorem basis_deleted : ∀ (k : Fin 2) (j : Fin 4),
    point (basisIndex k j) 0 = 0 ∧ point (basisIndex k j) 9 = 9 := by decide +kernel

theorem hexad_basis : ∀ (j : Fin 4) (x : Fin 24),
    x ∈ m22SourceOctad.val → point (basisIndex 0 j) x = x := by decide +kernel

theorem translation_basis : ∀ j : Fin 4, ∃ t : Fin 64,
    coreIndex t = basisIndex 1 j := by decide +kernel

theorem hexad_centralizer_check : ∀ i : Fin 1024,
    (point i 0 ∈ m22Pair ∧ point i 9 ∈ m22Pair) →
    (∀ (j : Fin 4) (x : Fin 3),
      point i (point (basisIndex 0 j) (testPoint x)) =
        point (basisIndex 0 j) (point i (testPoint x))) →
    ∀ x : Fin 24, x ∈ m22SourceOctad.val → point i x = x := by decide +kernel

theorem translation_centralizer_check : ∀ i : Fin 1024,
    (point i 0 ∈ m22Pair ∧ point i 9 ∈ m22Pair) →
    (∀ (j : Fin 4) (x : Fin 3),
      point i (point (basisIndex 1 j) (testPoint x)) =
        point (basisIndex 1 j) (point i (testPoint x))) →
    ∃ t : Fin 64, coreIndex t = i := by decide +kernel

end Sporadic.Mathieu.M22ChapterH.CompatibleSylow
