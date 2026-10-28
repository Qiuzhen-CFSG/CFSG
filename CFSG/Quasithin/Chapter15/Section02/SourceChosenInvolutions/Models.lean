module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import BenderSuzuki.MatrixGroups.SuzukiZero
public import Theory.GroupTheory.PrimeRankCyclicSylow

/-!
# The three surviving chosen-action carriers

These alternatives identify the literal action image with S3, D10, or the
concrete Suzuki matrix group Sz(2). Their Sylow two-subgroups are cyclic:
orders six and ten give a Sylow subgroup of order two; in Sz(2) the existing
root generator has order four and its cyclic subgroup has index five.
Sylow conjugacy then treats any specified Sylow subgroup of the action image.

Source: Aschbacher--Smith, 15.2.13(1) and 15.2.25(1), printed pp.1111,1118.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section02

/-- Actual carrier equivalences, used together with the original chosen action. -/
@[expose] def SmallChosenActionModels (D : Type*) [Group D] : Prop :=
  Nonempty (D ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (D ≃* DihedralGroup 5) ∨
    Nonempty (D ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)

variable {D : Type*} [Group D] [Finite D]

private theorem cyclic_sylow_conjugate (P Q : Sylow 2 D) (hc : IsCyclic Q) : IsCyclic P := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq D Q P
  let e : (Q : Subgroup D) ≃* ((g • Q : Sylow 2 D) : Subgroup D) :=
    equivMapOfInjective (Q : Subgroup D) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective
  have hh := e.isCyclic.mp hc
  rwa [hg] at hh

private theorem cyclic_sylow_small_card (P : Sylow 2 D)
    (hc : Nat.card D = 6 ∨ Nat.card D = 10) : IsCyclic P := by
  have hp : Nat.card P = 2 := by
    rw [P.card_eq_multiplicity]
    rcases hc with hc | hc <;> rw [hc] <;> decide +kernel
  exact isCyclic_of_prime_card hp

private theorem cyclic_sylow_twenty (P : Sylow 2 D)
    (hc : Nat.card D = 20) (t : D) (ht : orderOf t = 4) : IsCyclic P := by
  have hi : (zpowers t).index = 5 := by
    have hh := (zpowers t).index_mul_card
    rw [Nat.card_zpowers,ht,hc] at hh
    omega
  let Q := (IsPGroup.of_card (n := 2)
    (by rw [Nat.card_zpowers,ht]; decide : Nat.card (zpowers t) = 2^2)).toSylow
      (by rw [hi]; decide)
  exact cyclic_sylow_conjugate P Q (inferInstanceAs (IsCyclic (zpowers t)))

/-- Cyclicity belongs to the actual Sylow subgroup, not to a family label. -/
theorem SmallChosenActionModels.sylow_cyclic (h : SmallChosenActionModels D)
    (P : Sylow 2 D) : IsCyclic P := by
  unfold SmallChosenActionModels at h
  rcases h with hs | hd | hz
  · let e := Classical.choice hs
    apply cyclic_sylow_small_card P
    left
    rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]
    decide
  · let e := Classical.choice hd
    apply cyclic_sylow_small_card P
    right
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card]
    decide
  · let e := Classical.choice hz
    apply cyclic_sylow_twenty P
      ((Nat.card_congr e.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card)
      (e.symm BenderSuzuki.MatrixGroups.suzukiZeroRootGenerator)
    exact (orderOf_injective e.symm.toMonoidHom e.symm.injective _).trans
      BenderSuzuki.MatrixGroups.suzukiZeroRootGenerator_order

end CFSG.Quasithin.Chapter15.Section02
