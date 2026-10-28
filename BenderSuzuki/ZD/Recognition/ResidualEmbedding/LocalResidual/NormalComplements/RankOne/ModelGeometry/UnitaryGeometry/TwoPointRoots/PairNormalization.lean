module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Basic
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots.PairNormalization.Special

/-!
# Simultaneous unitary pair normalization and special two-point tori

The descendants export genuine conjugating elements for both SU₃ and PSU₃,
sending an arbitrary Sylow–outside-involution pair and its literal two-point
subgroup to the standard root, Weyl element and full torus.

Consequently the special-unitary two-point subgroup is cyclic of order q²−1.
Its inverted factor has order q−1 by the checked commutator calculation;
fixed/inverted factorization then gives a cyclic fixed factor of order q+1.
All intersections use the source convention B ∩ t⁻¹Bt.

Source: GLS4, Chapter 4, Lemma 3.2(c)–(e),(i), as used for SU₃
in Chapter 2, Section 16; concrete matrices from Huppert II.10.12.
-/

open Subgroup BenderSuzuki BenderSuzuki.PFAppendixIII BenderSuzuki.PFchapter1section1
namespace BenderSuzuki.ZD.RankOneModelGeometry
open _root_.BenderSuzuki.MatrixGroups HermitianForm External
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

include hn hcard hfixed hJ in
/-- The full special-unitary two-point subgroup, including the scalar center,
is a cyclic group of order q²−1. -/
public theorem unitary_special_twoPoint_torus (P : Sylow 2 J.specialSubgroup)
    (t : J.specialSubgroup) (ht : IsInvolution t)
    (htB : t ∉ normalizer (P : Set J.specialSubgroup)) :
    IsCyclic (twoPoint (normalizer (P : Set J.specialSubgroup)) t) ∧
      Nat.card (twoPoint (normalizer (P : Set J.specialSubgroup)) t) = (2 ^ n) ^ 2 - 1 := by
  obtain ⟨g, _, _, hm⟩ := PairNormalization.special_pair J hJ hn hcard hfixed P t ht htB
  let c := MulAut.conj g
  let D := twoPoint (normalizer (P : Set J.specialSubgroup)) t
  let e := (D.equivMapOfInjective c.toMonoidHom c.injective).trans
    (MulEquiv.subgroupCongr hm)
  have hc : IsCyclic (BorelTorus.specialTorus J hJ) :=
    isCyclic_of_surjective (hermitianTorusSU J hJ).rangeRestrict
      (hermitianTorusSU J hJ).rangeRestrict_surjective
  refine ⟨e.isCyclic.mpr hc, ?_⟩
  rw [Nat.card_congr e.toEquiv, BorelTorus.special_card, hcard]

include hn hcard hfixed hJ in
/-- The fixed factor in the special-unitary two-point torus is cyclic of order q+1. -/
public theorem unitary_special_fixed_torus (P : Sylow 2 J.specialSubgroup)
    (t : J.specialSubgroup) (ht : IsInvolution t)
    (htB : t ∉ normalizer (P : Set J.specialSubgroup)) :
    IsCyclic (twoPoint (normalizer (P : Set J.specialSubgroup)) t ⊓
      centralizer ({t} : Set _) : Subgroup _) ∧
      Nat.card (twoPoint (normalizer (P : Set J.specialSubgroup)) t ⊓
        centralizer ({t} : Set _) : Subgroup _) = 2 ^ n + 1 := by
  let B := normalizer (P : Set J.specialSubgroup)
  let D := twoPoint B t
  obtain ⟨hcD, hcardD⟩ := unitary_special_twoPoint_torus J hn hcard hfixed hJ P t ht htB
  let : IsCyclic D := hcD
  have hoddD : Odd (Nat.card D) := by
    rw [hcardD]
    exact Nat.Even.sub_odd (Nat.one_le_pow 2 (2 ^ n) (Nat.one_le_pow n 2 (by decide)))
      ((even_two.pow_of_ne_zero (by omega : n ≠ 0)).pow_of_ne_zero (by decide : 2 ≠ 0)) odd_one
  obtain ⟨T, hT, _, hTc⟩ := unitary_special_inverted_torus J hn hcard hfixed hJ P t ht htB
  have hm := card_fixed_mul_inverted D T t ht
    (inf_rightConjugate_mem_normalizer_of_isInvolution B ht) hoddD
    (fun x => (Set.ext_iff.mp hT x).trans and_assoc.symm)
  refine ⟨isCyclic_of_le (show D ⊓ centralizer ({t} : Set _) ≤ D from inf_le_left), ?_⟩
  have hq : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
  apply Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hq)
  calc
    _ = Nat.card D := by simpa only [hTc] using hm.symm
    _ = (2 ^ n) ^ 2 - 1 := hcardD
    _ = (2 ^ n + 1) * (2 ^ n - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ n) 1

end BenderSuzuki.ZD.RankOneModelGeometry
