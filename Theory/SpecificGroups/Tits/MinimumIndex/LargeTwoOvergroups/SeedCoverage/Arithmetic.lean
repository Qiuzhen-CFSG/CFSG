module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.Seeds
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.Packed
public import Theory.GroupTheory.SubgroupClosureWords
public import Theory.GroupTheory.SubgroupEnumerationBinary

/-!
# Small word certificates inside the marked Tits Sylow subgroup

The certified normal forms distinguish elements by their images of points 0
and 930. Surjectivity extends this test to arbitrary products in the Sylow
subgroup. Consequently two point computations certify each word equation in
a binary Schreier step; the whole 1600-point permutation need not be reduced.

Source: Parrott (1972), §5, p.683, and `Atlas1600SylowTwoEnumeration`.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration

abbrev S := atlas1600SylowTwoSubgroup

def element (n : Fin 2048) : S :=
  ⟨atlas1600SylowTwoNormalForm n, atlas1600SylowTwoNormalForm_mem n⟩

def pointHom : S →* Equiv.Perm (Fin 1600) where
  toFun x := x.val.val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem point_pair_ext (x y : S)
    (h : (pointHom x 0, pointHom x 930) = (pointHom y 0, pointHom y 930)) : x = y := by
  obtain ⟨i, hi⟩ := atlas1600SylowTwoNormalForm_surjective x.property
  obtain ⟨j, hj⟩ := atlas1600SylowTwoNormalForm_surjective y.property
  have he : i = j := atlas1600SylowTwoNormalForm_pair_injective (by
    exact (congrArg (fun z : Atlas1600Group => (z.val 0, z.val 930)) hi).trans
      (h.trans (congrArg (fun z : Atlas1600Group => (z.val 0, z.val 930)) hj).symm))
  apply Subtype.ext
  exact hi.symm.trans (he ▸ hj)

open OuterOddSubgroups.OverlapCentralizers in
def perm (n : Fin 2048) : Equiv.Perm (Fin 1600) :=
  Packed.perm 2 ^ (n.val % 2) *
    Packed.perm 3 ^ (n.val / 2 % 2) *
    Packed.perm 4 ^ (n.val / 4 % 4) *
    Packed.perm 5 ^ (n.val / 16 % 2) *
    Packed.perm 6 ^ (n.val / 32 % 4) *
    Packed.perm 7 ^ (n.val / 128 % 2) *
    Packed.perm 8 ^ (n.val / 256 % 4) *
    Packed.perm 9 ^ (n.val / 1024 % 2)

theorem pointHom_element (n : Fin 2048) : pointHom (element n) = perm n := by
  change (atlas1600SylowTwoNormalForm n).val = _
  rw [atlas1600SylowTwoNormalForm_val]
  simp only [perm, OuterOddSubgroups.OverlapCentralizers.Packed.perm_eq]
  rfl

theorem pointHom_word {n : Nat} (a : Fin n → S) (w : List (Fin n)) :
    pointHom (evalWord a w) = evalWord (fun i => pointHom (a i)) w := by
  induction w with
  | nil => exact pointHom.map_one
  | cons i w ih => simp only [evalWord, map_mul, ih]

/-- Finite equations between point pairs, in both containment directions. -/
def PointValid {n m : Nat} (w : ClosureWords n m)
    (a : Fin n → Equiv.Perm (Fin 1600)) (b : Fin m → Equiv.Perm (Fin 1600))
    (c : Equiv.Perm (Fin 1600)) : Prop :=
  (∀ k, ((evalWord b (w.forward k)) 0, (evalWord b (w.forward k)) 930) =
    ((c * a k * c⁻¹) 0, (c * a k * c⁻¹) 930)) ∧
  ∀ k, ((evalWord (fun j => c * a j * c⁻¹) (w.backward k)) 0,
      (evalWord (fun j => c * a j * c⁻¹) (w.backward k)) 930) = (b k 0, b k 930)

instance {n m : Nat} (w : ClosureWords n m)
    (a : Fin n → Equiv.Perm (Fin 1600)) (b : Fin m → Equiv.Perm (Fin 1600))
    (c : Equiv.Perm (Fin 1600)) : Decidable (PointValid w a b c) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem PointValid.sound {n m : Nat} (w : ClosureWords n m)
    (a : Fin n → S) (b : Fin m → S) (c : S)
    (h : PointValid w (fun i => pointHom (a i)) (fun i => pointHom (b i))
      (pointHom c)) :
    (Subgroup.closure (Set.range a)).map (MulAut.conj c).toMonoidHom =
      Subgroup.closure (Set.range b) := by
  apply w.sound
  constructor
  · intro k
    apply point_pair_ext
    simpa only [pointHom_word, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, map_mul, map_inv] using h.1 k
  · intro k
    apply point_pair_ext
    simpa only [pointHom_word, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, map_mul, map_inv] using h.2 k

end Tits.MinimumIndex.LargeTwoOvergroups.SeedCoverage
end
