module

public import Mathlib.GroupTheory.RegularWreathProduct
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.SpecificGroups.SymmetricFourConjugacy

/-!
# Diagonal subgroups in wreath-product centralizers

The diagonal base group commutes with the top group in a regular wreath
product. An actual marked model isomorphism therefore embeds that diagonal
group into the literal ambient intersection `M ∩ C_G(s)`.

For the symmetric group on four points, a double transposition is a product
of two elements whose cubes are one. Its diagonal image belongs to the
two-residual of this local centralizer. The same centralizer contains a
three-cycle, so is not a two-group. These proofs use small permutation
identities, without enumerating the wreath product or its subgroups.

Application: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 13.9.5, printed pp.970–971 (PDF pp.987–988). This constructs
the residual involution needed in the final fusion contradiction.
-/

public section

open Subgroup
namespace Theory.GroupTheory.WreathDiagonal
variable {D Q G : Type*} [Group D] [Group Q] [Group G]

/-- The diagonal copy of the base group in the regular wreath product. -/
def diagonal : D →* RegularWreathProduct D Q where
  toFun a := ⟨fun _ => a, 1⟩
  map_one' := rfl
  map_mul' a b := by ext <;> simp [RegularWreathProduct.mul_def]

theorem diagonal_injective : Function.Injective (diagonal : D →* RegularWreathProduct D Q) := by
  intro a b h
  exact congrArg (fun x : RegularWreathProduct D Q => x.left 1) h

theorem diagonal_commutes (a : D) (q : Q) :
    Commute (diagonal a) (RegularWreathProduct.inl q : RegularWreathProduct D Q) := by
  change diagonal a * RegularWreathProduct.inl q = RegularWreathProduct.inl q * diagonal a
  ext <;> simp [diagonal]

/-- The diagonal copy in the literal local centralizer of a marked top-group
 element. Normality of the local subgroup in the ambient group is not needed. -/
def localDiagonal (M : Subgroup G) (e : M ≃* RegularWreathProduct D Q)
    (s : M) (q : Q) (hs : e s = RegularWreathProduct.inl q) :
    D →* (M ⊓ centralizer ({(s : G)} : Set G) : Subgroup G) :=
  (M.subtype.comp (e.symm.toMonoidHom.comp diagonal)).codRestrict _ (by
    intro a
    refine ⟨(e.symm (diagonal a)).property, ?_⟩
    apply mem_centralizer_singleton_iff.mpr
    change ((e.symm (diagonal a) * s : M) : G) = ((s * e.symm (diagonal a) : M) : G)
    congr 1
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply, hs] using (diagonal_commutes a q).eq)

theorem localDiagonal_injective (M : Subgroup G) (e : M ≃* RegularWreathProduct D Q)
    (s : M) (q : Q) (hs : e s = RegularWreathProduct.inl q) :
    Function.Injective (localDiagonal M e s q hs) := by
  intro a b h
  apply diagonal_injective (Q := Q)
  apply e.symm.injective
  exact Subtype.ext (congrArg (fun x : (M ⊓ centralizer ({(s : G)} : Set G) : Subgroup G) => (x : G)) h)

abbrev doubleTransposition : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

theorem doubleTransposition_order : orderOf doubleTransposition = 2 :=
  orderOf_eq_prime (by decide : doubleTransposition ^ 2 = 1) (by decide)

theorem doubleTransposition_mem_twoResidual :
    doubleTransposition ∈ pResidual 2 (Equiv.Perm (Fin 4)) := by
  let a : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2
  let b := a⁻¹ * doubleTransposition
  have ha : a ^ 3 = 1 := by decide
  have hb : b ^ 3 = 1 := by decide
  have hmem (x : Equiv.Perm (Fin 4)) (hx : x ^ 3 = 1) :
      x ∈ pResidual 2 (Equiv.Perm (Fin 4)) :=
    mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hx))
  simpa only [b, mul_inv_cancel_left] using
    (pResidual 2 (Equiv.Perm (Fin 4))).mul_mem (hmem a ha) (hmem b hb)

/-- The marked diagonal double transposition belongs to the two-residual of
 the local centralizer of the top-group element. -/
theorem marked_involution_mem_local_residual
    (M : Subgroup G) (e : M ≃* RegularWreathProduct (Equiv.Perm (Fin 4)) Q)
    (s z : M) (q : Q) (hs : e s = RegularWreathProduct.inl q)
    (hz : e z = diagonal doubleTransposition) :
    (z : G) ∈ (pResidual 2 (M ⊓ centralizer ({(s : G)} : Set G) : Subgroup G)).map
      (M ⊓ centralizer ({(s : G)} : Set G)).subtype := by
  let f := localDiagonal M e s q hs
  have hmem : f doubleTransposition ∈ pResidual 2 (M ⊓ centralizer ({(s : G)} : Set G) : Subgroup G) :=
    map_pResidual_le 2 f (mem_map.mpr ⟨doubleTransposition, doubleTransposition_mem_twoResidual, rfl⟩)
  refine mem_map.mpr ⟨f doubleTransposition, hmem, ?_⟩
  change ((e.symm (diagonal doubleTransposition) : M) : G) = (z : G)
  rw [← hz, e.symm_apply_apply]

/-- The same local centralizer contains an element of order three. -/
theorem local_centralizer_not_twoGroup
    (M : Subgroup G) (e : M ≃* RegularWreathProduct (Equiv.Perm (Fin 4)) Q)
    (s : M) (q : Q) (hs : e s = RegularWreathProduct.inl q) :
    ¬ IsPGroup 2 (M ⊓ centralizer ({(s : G)} : Set G) : Subgroup G) := by
  intro hp
  have hS := hp.of_injective (localDiagonal M e s q hs)
    (localDiagonal_injective M e s q hs)
  obtain ⟨n, hn⟩ := hS.exists_orderOf_dvd_pow SymmetricFourConjugacy.threeCycle
  rw [SymmetricFourConjugacy.orderOf_threeCycle] at hn
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hn)

end Theory.GroupTheory.WreathDiagonal
