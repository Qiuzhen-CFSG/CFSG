module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The two cubic centralizers on six letters

For a single three-cycle, its centralizer is its cyclic group times the
symmetric group on the three fixed letters. For two three-cycles, diagonal
rotation is the central factor, while antidiagonal rotation and interchange
of the triples form S3. Explicit maps from C3 × S3 preserve sign; injectivity
and the cycle-type centralizer formula prove coverage. The kernel checks
involve only eighteen words, never all of A10.

Source: Held, DOI 10.1215/ijm/1256053756, Lemma 5.4, pp.236–237.
-/

public section

open Subgroup Equiv Equiv.Perm
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry.ThreeCentralizer.Tail
abbrev C3 := Multiplicative (ZMod 3)
@[expose] def a : Perm (Fin 6) := swap 0 1 * swap 1 2
@[expose] def b : Perm (Fin 6) := swap 3 4 * swap 4 5
@[expose] def root : Bool → Perm (Fin 6)
  | false => a
  | true => a * b
@[expose] def rotation : Bool → Perm (Fin 6)
  | false => b
  | true => a * b⁻¹
@[expose] def flip : Bool → Perm (Fin 6)
  | false => swap 3 4
  | true => swap 0 3 * swap 1 4 * swap 2 5
@[expose] def lift (t : Bool) (s : Perm (Fin 3)) : Perm (Fin 6) :=
  if sign s = 1 then rotation t ^ (s 0).val
  else flip t * rotation t ^ ((swap 0 1) (s 0)).val

@[expose] def word (t : Bool) (x : C3 × Perm (Fin 3)) : Perm (Fin 6) :=
  root t ^ x.1.toAdd.val * lift t x.2

theorem word_one : ∀ t, word t 1 = 1 := by decide +kernel
theorem word_mul : ∀ t x y, word t (x * y) = word t x * word t y := by decide +kernel
theorem word_comm : ∀ t x, word t x * root t = root t * word t x := by decide +kernel
theorem word_sign : ∀ t x, sign (word t x) = sign x.2 := by decide +kernel
theorem word_inj : ∀ t, Function.Injective (word t) := by
  have h : ∀ t, Function.Injective (fun x => (word t x 0, word t x 3, word t x 4)) := by decide +kernel
  intro t x y he
  exact h t (congrArg (fun p : Perm (Fin 6) => (p 0, p 3, p 4)) he)

abbrev Centralizer (t : Bool) := centralizer ({root t} : Set (Perm (Fin 6)))

@[expose] def hom (t : Bool) : C3 × Perm (Fin 3) →* Centralizer t where
  toFun x := ⟨word t x, mem_centralizer_singleton_iff.mpr (word_comm t x)⟩
  map_one' := Subtype.ext (word_one t)
  map_mul' x y := Subtype.ext (word_mul t x y)

theorem centralizer_card (t : Bool) : Nat.card (Centralizer t) = 18 := by
  rw [nat_card_centralizer]
  cases t
  · have h : (root false).cycleType = {3} := by decide +kernel
    rw [h]
    norm_num
  · have h : (root true).cycleType = {3, 3} := by decide +kernel
    rw [h]
    norm_num

@[expose] noncomputable def equiv (t : Bool) : C3 × Perm (Fin 3) ≃* Centralizer t :=
  MulEquiv.ofBijective (hom t) ((show Function.Injective (hom t) from
    fun _ _ h => word_inj t (congrArg Subtype.val h)).bijective_of_nat_card_le (by
      rw [centralizer_card]
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial, C3]))

theorem equiv_sign (t : Bool) (x : C3 × Perm (Fin 3)) :
    sign (equiv t x).val = sign x.2 := word_sign t x

theorem equiv_root (t : Bool) :
    (equiv t (Multiplicative.ofAdd 1, 1)).val = root t := by
  exact (by decide +kernel : ∀ t, word t (Multiplicative.ofAdd 1, 1) = root t) t

theorem root_sign : ∀ t, sign (root t) = 1 := by decide +kernel

theorem root_ne_one : ∀ t, root t ≠ 1 := by decide +kernel

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry.ThreeCentralizer.Tail
