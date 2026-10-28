module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections.Common
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic

/-!
# The dihedral local E1 calculation

Reduction of rotation coordinates modulo p maps D₄p onto D₂p. Its kernel
has order two, is central, and is the two-core, because the normal cyclic
subgroup of order p in D₂p is self-centralizing. A four-group therefore
has a nontrivial image, of order two, which generates the odd core by
commutators. All maps are transported through the supplied actual model
isomorphism before identifying the intrinsic quotient and actor.

Source: Aschbacher–Smith, E.1.2(E1) and E.1.5, printed p.210.
-/

public section

open Subgroup DihedralGroup
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections

private def rotations (p : ℕ) : Subgroup (DihedralGroup p) := zpowers (r 1)

private theorem rotations_card (p : ℕ) : Nat.card (rotations p) = p := by
  simp only [rotations, Nat.card_zpowers, orderOf_r_one]

private theorem rotation_mem {p : ℕ} [NeZero p] (i : ZMod p) : r i ∈ rotations p := by
  refine mem_zpowers_iff.mpr ⟨i.val, ?_⟩
  simp

private instance rotations_normal (p : ℕ) [NeZero p] : (rotations p).Normal := by
  apply Subgroup.normal_of_index_eq_two
  have hh := (rotations p).card_mul_index
  rw [rotations_card, DihedralGroup.nat_card] at hh
  nlinarith [NeZero.pos p]

private theorem rotations_selfCentralizing {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    centralizer (rotations p : Set (DihedralGroup p)) ≤ rotations p := by
  let : Fact p.Prime := ⟨hp⟩
  intro x hx
  cases x with
  | r i => exact rotation_mem i
  | sr i =>
    have hh := mem_centralizer_iff.mp hx (r 1) (mem_zpowers (r 1))
    have he : i - 1 = i + 1 := DihedralGroup.sr.inj hh
    have hz : (1 : ZMod p) + 1 = 0 := by linear_combination -he
    exact False.elim (one_ne_zero ((ZMod.add_self_eq_zero_iff_eq_zero ho).mp hz))

private def dihedralReduction (p : ℕ) : DihedralGroup (2 * p) →* DihedralGroup p :=
  let f := ZMod.castHom (show p ∣ 2 * p from dvd_mul_left p 2) (ZMod p)
  { toFun := fun x => match x with
      | .r i => .r (f i)
      | .sr i => .sr (f i)
    map_one' := by change r (f 0) = r 0; rw [map_zero]
    map_mul' := by
      rintro (i | i) (j | j) <;>
        simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr, map_add, map_sub] }

private theorem dihedralReduction_surjective (p : ℕ) :
    Function.Surjective (dihedralReduction p) := by
  have hf := ZMod.castHom_surjective (show p ∣ 2 * p from dvd_mul_left p 2)
  rintro (i | i)
  · obtain ⟨j, rfl⟩ := hf i
    exact ⟨r j, rfl⟩
  · obtain ⟨j, rfl⟩ := hf i
    exact ⟨sr j, rfl⟩

private theorem dihedralReduction_kernel_card {p : ℕ} (hp : p.Prime) :
    Nat.card (dihedralReduction p).ker = 2 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero (2 * p) := ⟨Nat.mul_ne_zero (by decide) hp.ne_zero⟩
  have hh := (dihedralReduction p).ker.card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (dihedralReduction_surjective p)).toEquiv, DihedralGroup.nat_card,
    DihedralGroup.nat_card] at hh
  nlinarith [hp.pos]

private theorem dihedralReduction_kernel_eq {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    (dihedralReduction p).ker = pCore 2 (DihedralGroup (2 * p)) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero (2 * p) := ⟨Nat.mul_ne_zero (by decide) hp.ne_zero⟩
  have hb : pCore 2 (DihedralGroup p) = ⊥ :=
    twoCore_eq_bot hp ho (rotations p) (rotations_card p) (rotations_selfCentralizing hp ho)
  have hk : IsPGroup 2 (dihedralReduction p).ker :=
    IsPGroup.of_card (n := 1) (by simpa using dihedralReduction_kernel_card hp)
  have hh := (dihedralReduction p).comap_pCore_of_ker_isPGroup
    (dihedralReduction_surjective p) hk
  simpa only [hb, MonoidHom.comap_bot] using hh

/-- The literal two-core of D₄p is central of order two, with quotient D₂p. -/
theorem dihedral_twoCore {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    Nat.card (pCore 2 (DihedralGroup (2 * p))) = 2 ∧
      pCore 2 (DihedralGroup (2 * p)) ≤ center (DihedralGroup (2 * p)) ∧
      Nonempty ((DihedralGroup (2 * p) ⧸ pCore 2 (DihedralGroup (2 * p))) ≃*
        DihedralGroup p) := by
  have hk := dihedralReduction_kernel_eq hp ho
  have hc : Nat.card (pCore 2 (DihedralGroup (2 * p))) = 2 :=
    hk ▸ dihedralReduction_kernel_card hp
  refine ⟨hc, central_of_normal_card_two _ hc, ?_⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (dihedralReduction_surjective p))⟩

/-- Every elementary four-group in an actual D₄p model gives E1 at p. -/
theorem dihedral_intrinsic {X : Type*} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (B : Subgroup X) [IsElementaryAbelian 2 B] (hB : Nat.card B = 4)
    (e : X ≃* DihedralGroup (2 * p)) :
    let Q := X ⧸ pCore 2 X
    let a := B.map (QuotientGroup.mk' (pCore 2 X))
    IsPGroup 2 (Q ⧸ pCore p Q) ∧ pCore p Q ≠ ⊥ ∧
      pCore p Q = ⁅pCore p Q, a⁆ ∧ Group.rank a = 1 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero (2 * p) := ⟨Nat.mul_ne_zero (by decide) hp.ne_zero⟩
  let f : X →* DihedralGroup p := (dihedralReduction p).comp e.toMonoidHom
  have hf : Function.Surjective f := (dihedralReduction_surjective p).comp e.surjective
  have hX : Nat.card X = 2 * (2 * p) :=
    (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
  have hkcard : Nat.card f.ker = 2 := by
    have hh := f.ker.card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
      hX, DihedralGroup.nat_card] at hh
    nlinarith [hp.pos]
  have hk : f.ker = pCore 2 X := by
    have hh := f.comap_pCore_of_ker_isPGroup hf
      (IsPGroup.of_card (n := 1) (by simpa using hkcard))
    have hb := twoCore_eq_bot hp ho (rotations p) (rotations_card p)
      (rotations_selfCentralizing hp ho)
    simpa only [hb, MonoidHom.comap_bot] using hh
  let : IsElementaryAbelian 2 (B.map f) := IsElementaryAbelian.map f
  have hne : B.map f ≠ ⊥ := by
    intro hh
    have hle : B ≤ f.ker := (map_eq_bot_iff B).mp hh
    have hcard := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
    rw [hB, hkcard] at hcard
    omega
  apply intrinsic_of_epimorphism B f hf hk
  exact primeSection hp ho (rotations p) (rotations_card p)
    DihedralGroup.nat_card (rotations_selfCentralizing hp ho) (B.map f) hne

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections
