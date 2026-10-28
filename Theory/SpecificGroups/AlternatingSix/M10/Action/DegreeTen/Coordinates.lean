module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Identification.Generators
public import Theory.AtlasPort.ExceptionalIsomorphisms.TriplePartitions
public import Mathlib.Algebra.Field.ZMod

/-!
# Ten explicit nine-groups and their generator images

Conjugate the product of the two disjoint three-cycles by the ten listed
relabelings of the complementary triples in `TriplePartitions`. Each range
has order nine, and the first cycle distinguishes all ten ranges. The last
generator is the actual pentad automorphism following conjugation by the
marked twist and transposition. Its two generator images in every nine-group
are checked by kernel reduction, as are the three natural generator images.

These small certificates support the intrinsic Sylow action calculation in
`DegreeTen.SylowModel`; they do not enumerate the automorphism carrier.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), the degree-ten action used in 4.10, pp.41–42. The complementary
triple numbering is from the attributed ATLAS port `TriplePartitions`.
-/

@[expose] public section

open Subgroup
namespace AlternatingSix.M10.Action.DegreeTen
open ShadowLocal
open Atlas.Comparisons.Exceptional.TriplePartitions
abbrev E := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)
def baseEmbedding : E →* Sym where
  toFun x := firstCyclePerm ^ x.1.toAdd.val * secondCyclePerm ^ x.2.toAdd.val
  map_one' := rfl
  map_mul' := by decide +kernel

theorem baseEmbedding_injective : Function.Injective baseEmbedding := by decide +kernel

def relabel (i : Fin 10) : Sym where
  toFun := ![![0,1,3,2,4,5],
    ![0,4,5,1,2,3],
    ![0,2,3,1,4,5],
    ![0,1,4,2,3,5],
    ![0,3,5,1,2,4],
    ![0,2,4,1,3,5],
    ![0,1,5,2,3,4],
    ![0,3,4,1,2,5],
    ![0,2,5,1,3,4],
    ![0,1,2,3,4,5]] i
  invFun := ![![0,1,3,2,4,5],
    ![0,3,4,5,1,2],
    ![0,3,1,2,4,5],
    ![0,1,3,4,2,5],
    ![0,3,4,1,5,2],
    ![0,3,1,4,2,5],
    ![0,1,3,4,5,2],
    ![0,3,4,1,2,5],
    ![0,3,1,4,5,2],
    ![0,1,2,3,4,5]] i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

def embedding (i : Fin 10) : E →* Sym :=
  (MulAut.conj (relabel i)).toMonoidHom.comp baseEmbedding

def nineGroup (i : Fin 10) : Subgroup Sym := (embedding i).range

theorem card_nineGroup (i : Fin 10) : Nat.card (nineGroup i) = 9 := by
  have hi : Function.Injective (embedding i) :=
    (MulAut.conj (relabel i)).injective.comp baseEmbedding_injective
  rw [nineGroup, ← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv,
    Nat.card_eq_fintype_card]
  decide +kernel

def first : E := (Multiplicative.ofAdd 1, 1)
def second : E := (1, Multiplicative.ofAdd 1)

theorem embedding_separates : ∀ (i j : Fin 10) (x : E),
    embedding j x = embedding i first → i = j := by decide +kernel

/-- The action of the literal exceptional generator on the ten nine-groups. -/
def exceptional : Equiv.Perm (Fin 10) where
  toFun := ![3,6,4,2,1,8,9,0,5,7]
  invFun := ![7,4,3,0,2,8,1,9,5,6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def permutation : Fin 4 → Equiv.Perm (Fin 10) := ![shiftOne, shiftOmega, invert, exceptional]

def generatorHom : Fin 4 → (Sym →* Sym) := ![
  (MulAut.conj firstCyclePerm).toMonoidHom,
  (MulAut.conj secondCyclePerm).toMonoidHom,
  (MulAut.conj doubleSwapPerm).toMonoidHom,
  GLS3.Chapter5.outerHom.comp (MulAut.conj
    (Identification.twist * Identification.transpositionPerm)).toMonoidHom]

def imageCoordinates : Fin 4 → Fin 10 → Fin 2 → E :=
  ![![![(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1),(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0)],
    ![(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1),(Multiplicative.ofAdd 2, Multiplicative.ofAdd 0)],
    ![(Multiplicative.ofAdd 2, Multiplicative.ofAdd 0),(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)],
    ![(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1),(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0)],
    ![(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1),(Multiplicative.ofAdd 2, Multiplicative.ofAdd 0)],
    ![(Multiplicative.ofAdd 2, Multiplicative.ofAdd 0),(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)],
    ![(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1),(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0)],
    ![(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1),(Multiplicative.ofAdd 2, Multiplicative.ofAdd 0)],
    ![(Multiplicative.ofAdd 2, Multiplicative.ofAdd 0),(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)],
    ![(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0),(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)]],
    ![![(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0),(Multiplicative.ofAdd 0, Multiplicative.ofAdd 2)],
    ![(Multiplicative.ofAdd 2, Multiplicative.ofAdd 0),(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)],
    ![(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0),(Multiplicative.ofAdd 0, Multiplicative.ofAdd 2)],
    ![(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0),(Multiplicative.ofAdd 0, Multiplicative.ofAdd 2)],
    ![(Multiplicative.ofAdd 2, Multiplicative.ofAdd 0),(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)],
    ![(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0),(Multiplicative.ofAdd 0, Multiplicative.ofAdd 2)],
    ![(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0),(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)],
    ![(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0),(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)],
    ![(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0),(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)],
    ![(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0),(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)]],
    ![![(Multiplicative.ofAdd 2, Multiplicative.ofAdd 0),(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)],
    ![(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1),(Multiplicative.ofAdd 2, Multiplicative.ofAdd 0)],
    ![(Multiplicative.ofAdd 0, Multiplicative.ofAdd 2),(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0)],
    ![(Multiplicative.ofAdd 2, Multiplicative.ofAdd 0),(Multiplicative.ofAdd 0, Multiplicative.ofAdd 2)],
    ![(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1),(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0)],
    ![(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1),(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0)],
    ![(Multiplicative.ofAdd 2, Multiplicative.ofAdd 0),(Multiplicative.ofAdd 0, Multiplicative.ofAdd 2)],
    ![(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1),(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0)],
    ![(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1),(Multiplicative.ofAdd 1, Multiplicative.ofAdd 0)],
    ![(Multiplicative.ofAdd 2, Multiplicative.ofAdd 0),(Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)]],
    ![![(Multiplicative.ofAdd 1, Multiplicative.ofAdd 1),(Multiplicative.ofAdd 2, Multiplicative.ofAdd 1)],
    ![(Multiplicative.ofAdd 1, Multiplicative.ofAdd 2),(Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)],
    ![(Multiplicative.ofAdd 2, Multiplicative.ofAdd 1),(Multiplicative.ofAdd 2, Multiplicative.ofAdd 2)],
    ![(Multiplicative.ofAdd 2, Multiplicative.ofAdd 2),(Multiplicative.ofAdd 2, Multiplicative.ofAdd 1)],
    ![(Multiplicative.ofAdd 2, Multiplicative.ofAdd 1),(Multiplicative.ofAdd 2, Multiplicative.ofAdd 2)],
    ![(Multiplicative.ofAdd 1, Multiplicative.ofAdd 2),(Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)],
    ![(Multiplicative.ofAdd 2, Multiplicative.ofAdd 1),(Multiplicative.ofAdd 2, Multiplicative.ofAdd 2)],
    ![(Multiplicative.ofAdd 1, Multiplicative.ofAdd 1),(Multiplicative.ofAdd 2, Multiplicative.ofAdd 1)],
    ![(Multiplicative.ofAdd 2, Multiplicative.ofAdd 1),(Multiplicative.ofAdd 2, Multiplicative.ofAdd 2)],
    ![(Multiplicative.ofAdd 2, Multiplicative.ofAdd 1),(Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)]]]

theorem generator_images (k : Fin 4) (i : Fin 10) (a : Fin 2) :
    generatorHom k (embedding i (![first, second] a)) =
      embedding (permutation k i) (imageCoordinates k i a) := by
  revert k i a
  decide +kernel

theorem embedding_even (i : Fin 10) (x : E) :
    embedding i x ∈ alternatingGroup (Fin 6) := by
  change Equiv.Perm.sign (embedding i x) = 1
  have h : ∀ (i : Fin 10) (x : E), Equiv.Perm.sign (embedding i x) = 1 := by decide +kernel
  exact h i x

end AlternatingSix.M10.Action.DegreeTen
