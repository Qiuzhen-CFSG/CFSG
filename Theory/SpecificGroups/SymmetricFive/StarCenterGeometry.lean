module

public import Theory.SpecificGroups.SymmetricFiveSylow
public import Mathlib.Tactic.FinCases
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The two Sylow five-subgroups inverted by an even involution in S₅

For (01)(23), the two inverted pentagons are (01243) and (01342).
A checked five-point certificate places every inverted five-cycle in one
of their cyclic subgroups. Every Sylow five-subgroup has order five, so
this gives a bijection with two elements. Conjugation transports the count
to any even involution, using only finite permutation calculations.
No subsets or subgroup lattice are enumerated.

Source: Aschbacher–Smith, J.4.1(2), printed p.440.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.SpecificGroups.SymmetricFive.StarCenterGeometry
private abbrev D := Equiv.Perm (Fin 5)
private instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
private def z : D := Equiv.swap 0 1 * Equiv.swap 2 3
private def cycle (i : Fin 2) : D :=
  ![Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 4 3,
    Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 4 * Equiv.swap 4 2] i
private def word (i : Fin 2) (k : Fin 5) : D := cycle i ^ k.val
private def five (i : Fin 2) : Subgroup D where
  carrier := Set.range (word i)
  one_mem' := ⟨0,by simp [word]⟩
  mul_mem' := by
    have h : ∀ i j k, ∃ l, word i j * word i k = word i l := by decide +kernel
    rintro x y ⟨j,rfl⟩ ⟨k,rfl⟩
    obtain ⟨l,hl⟩ := h i j k
    exact ⟨l,hl.symm⟩
  inv_mem' := by
    have h : ∀ i j, ∃ k, (word i j)⁻¹ = word i k := by decide +kernel
    rintro x ⟨j,rfl⟩
    obtain ⟨k,hk⟩ := h i j
    exact ⟨k,hk.symm⟩
private theorem five_card (i : Fin 2) : Nat.card (five i) = 5 := by
  have h : ∀ i, Function.Injective (word i) := by decide +kernel
  change Nat.card (Set.range (word i)) = 5
  rw [← Nat.card_congr (Equiv.ofInjective _ (h i))]
  simp
private noncomputable def fiveSylow (i : Fin 2) : Sylow 5 D :=
  Sylow.ofCard (five i) (by
    rw [five_card,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide +kernel)
private theorem sylow_five_card (P : Sylow 5 D) : Nat.card P = 5 := by
  rw [P.card_eq_multiplicity,Nat.card_eq_fintype_card,Fintype.card_perm]
  decide +kernel

private theorem inverted_word : ∀ i k, z * word i k * z⁻¹ = (word i k)⁻¹ := by
  decide +kernel
private theorem inverted_cover : ∀ x : D, x ^ 5 = 1 → x ≠ 1 →
    z * x * z⁻¹ = x⁻¹ → ∃ i k, x = word i k := by
  decide +kernel
private theorem separated_words : ∀ i j k, cycle i = word j k → i=j := by
  decide +kernel
private theorem fiveSylow_injective : Function.Injective fiveSylow := by
  intro i j h
  have hm : cycle i ∈ (fiveSylow j : Subgroup D) := by
    rw [← h]
    exact ⟨1,by simp [word]⟩
  obtain ⟨k,hk⟩ := hm
  exact separated_words i j k hk.symm

private theorem standard_count :
    Nat.card {P : Sylow 5 D // ∀ x ∈ (P : Subgroup D), z*x*z⁻¹=x⁻¹} = 2 := by
  let f : Fin 2 → {P : Sylow 5 D // ∀ x ∈ (P : Subgroup D), z*x*z⁻¹=x⁻¹} :=
    fun i => ⟨fiveSylow i,by rintro x ⟨k,rfl⟩; exact inverted_word i k⟩
  have hi : Function.Injective f := fun i j h =>
    fiveSylow_injective (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    rintro ⟨P,hP⟩
    obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := P) 5 (by rw [sylow_five_card P])
    have hao : orderOf (a : D) = 5 := (orderOf_coe a).trans ha
    have han : (a : D) ≠ 1 := by intro h; simp [h] at hao
    obtain ⟨i,k,hk⟩ := inverted_cover a (by simpa only [hao] using pow_orderOf_eq_one (a : D)) han
      (hP a a.property)
    have hA : zpowers (a : D) = (P : Subgroup D) :=
      eq_of_le_of_card_ge (zpowers_le.mpr a.property) (by
        rw [Nat.card_zpowers,hao,sylow_five_card P])
    have hPi : (P : Subgroup D) = (fiveSylow i : Subgroup D) := by
      apply eq_of_le_of_card_ge
      · rw [← hA]
        exact zpowers_le.mpr ⟨k,hk.symm⟩
      · rw [sylow_five_card P,sylow_five_card]
    exact ⟨i,Subtype.ext (SetLike.coe_injective (congrArg (fun A : Subgroup D => (A : Set D)) hPi.symm))⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)).symm.trans (Nat.card_fin 2)

private theorem involution_conjugator : ∀ v : D, v^2=1 → v≠1 → v.sign=1 →
    ∃ g : D, g*v*g⁻¹=z := by
  decide +kernel

private theorem inverts_conjugate_iff (g v : D) (P : Sylow 5 D) :
    (∀ x ∈ ((g • P : Sylow 5 D) : Subgroup D),
      (g*v*g⁻¹)*x*(g*v*g⁻¹)⁻¹=x⁻¹) ↔
      ∀ x ∈ (P : Subgroup D), v*x*v⁻¹=x⁻¹ := by
  rw [Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def]
  constructor
  · intro h x hx
    apply (MulAut.conj g).injective
    have hh := h ((MulAut.conj g) x) (mem_map_of_mem _ hx)
    simpa only [map_mul,map_inv,MulAut.conj_apply] using hh
  · rintro h x ⟨y,hy,rfl⟩
    change (g*v*g⁻¹)*(g*y*g⁻¹)*(g*v*g⁻¹)⁻¹=(g*y*g⁻¹)⁻¹
    have hh := congrArg (MulAut.conj g) (h y hy)
    simpa only [map_mul,map_inv,MulAut.conj_apply] using hh

/-- Every even involution in S₅ inverts exactly two Sylow five-subgroups. -/
theorem inverted_sylow_count (v : Equiv.Perm (Fin 5)) (ho : orderOf v = 2)
    (hv : v ∈ alternatingGroup (Fin 5)) :
    Nat.card {P : Sylow 5 (Equiv.Perm (Fin 5)) //
      ∀ x ∈ (P : Subgroup _), v*x*v⁻¹=x⁻¹} = 2 := by
  obtain ⟨g,hg⟩ := involution_conjugator v
    ((orderOf_eq_prime_iff.mp ho).1) ((orderOf_eq_prime_iff.mp ho).2)
    (Equiv.Perm.mem_alternatingGroup.mp hv)
  let e := Equiv.subtypeEquiv (MulAction.toPerm g : Sylow 5 D ≃ Sylow 5 D)
    (p := fun P : Sylow 5 D => ∀ x ∈ (P : Subgroup D), v*x*v⁻¹=x⁻¹)
    (q := fun P : Sylow 5 D => ∀ x ∈ (P : Subgroup D), z*x*z⁻¹=x⁻¹)
    (fun P => by
      change (∀ x ∈ (P : Subgroup D), v*x*v⁻¹=x⁻¹) ↔
        ∀ x ∈ ((g • P : Sylow 5 D) : Subgroup D), z*x*z⁻¹=x⁻¹
      rw [← hg]
      exact (inverts_conjugate_iff g v P).symm)
  exact (Nat.card_congr e).trans standard_count
end Theory.SpecificGroups.SymmetricFive.StarCenterGeometry
