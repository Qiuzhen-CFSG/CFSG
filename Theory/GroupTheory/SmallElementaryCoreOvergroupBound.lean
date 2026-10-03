module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.ElementaryEightAutomorphismBound
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable

/-!
# Small self-centralizing elementary-core overgroups

Conjugation on a normal self-centralizing elementary abelian subgroup has
kernel exactly that subgroup. The image has a Sylow two-subgroup of order
two under the given overgroup hypothesis. In order four its order is bounded
by the Klein-four automorphism count. In order eight the imported automorphism
subgroup theorem bounds the image by six: the ambient automorphism group has
order 168, and oddness of seven-subgroup normalizers excludes the excessive
candidate image orders 14 and 42. Multiplying by the kernel order gives the
overgroup bound. Solvability passes to the image through the conjugation map.

This supplies the missing cardinal argument in Stellmacher Section 11,
`refs/latex/stellmacher-n-group.tex`, lines 2076–2081. No model subgroup is
assumed normal. The public result retains the finite solvable hypothesis and
the prescribed Sylow order used by the small-model normalizer argument.
-/

open scoped IsMulCommutative

universe u

private theorem conjugation_ker_eq
    {K : Type*} [Group K] (A : Subgroup K) [A.Normal]
    [IsElementaryAbelian 2 A]
    (hcent : Subgroup.centralizer (A : Set K) ≤ A) :
    (MulAut.conjNormal (H := A)).ker = A := by
  apply le_antisymm
  · intro element helement
    apply hcent
    rw [Subgroup.mem_centralizer_iff]
    intro member hmember
    have hfix := congrArg (fun automorphism : MulAut A =>
      (automorphism ⟨member, hmember⟩ : K)) helement
    change element * member * element⁻¹ = member at hfix
    calc
      member * element = (element * member * element⁻¹) * element := by rw [hfix]
      _ = element * member := by simp [mul_assoc]
  · intro element helement
    rw [MonoidHom.mem_ker]
    ext member
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    have hcomm := congrArg (fun member : A => (member : K))
      (mul_comm (⟨element, helement⟩ : A) member)
    change element * (member : K) = (member : K) * element at hcomm
    rw [hcomm]
    simp [mul_assoc]

public theorem card_le_six_mul_of_small_elementary_core
    {K : Type u} [Group K] [Finite K] [Group.IsSolvable K]
    (A : Subgroup K) [A.Normal] [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 4 ∨ Nat.card A = 8)
    (hcent : Subgroup.centralizer (A : Set K) ≤ A)
    (hSylow : ∃ T : Sylow 2 K, Nat.card T = 2 * Nat.card A) :
    Nat.card K ≤ 6 * Nat.card A := by
  classical
  let conjugation : K →* MulAut A := MulAut.conjNormal
  have hker : conjugation.ker = A := conjugation_ker_eq A hcent
  have hfactor : Nat.card A * Nat.card conjugation.range = Nat.card K := by
    rw [← Subgroup.index_ker, hker]
    exact A.card_mul_index
  have himage : Nat.card conjugation.range ≤ 6 := by
    rcases hcard with hfour | height
    · let : Nontrivial A := not_subsingleton_iff_nontrivial.mp (by
        intro hsubsingleton
        have hone : Nat.card A = 1 := Nat.card_eq_one_iff_unique.mpr
          ⟨hsubsingleton, inferInstance⟩
        omega)
      let : IsKleinFour A := ⟨hfour, IsElementaryAbelian.exponent_eq_prime⟩
      calc
        Nat.card conjugation.range ≤ Nat.card (MulAut A) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
        _ = 6 := IsKleinFour.card_mulAut A
    · let : Group.IsSolvable conjugation.range :=
        Group.isSolvable_of_surjective conjugation.rangeRestrict_surjective
      apply card_le_six_of_elementary_eight_automorphisms A height conjugation.range
      obtain ⟨sylow, hsylow⟩ := hSylow
      let imageSylow := sylow.mapSurjective conjugation.rangeRestrict_surjective
      refine ⟨imageSylow, ?_⟩
      have hle : A ≤ sylow := (IsElementaryAbelian.isPGroup 2 A).le_sylow_of_normal sylow
      have hsubcard : Nat.card (A.subgroupOf (sylow : Subgroup K)) = Nat.card A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
      have hmul := (A.subgroupOf (sylow : Subgroup K)).card_mul_index
      rw [hsubcard, hsylow] at hmul
      have hindex : (A.subgroupOf (sylow : Subgroup K)).index = Nat.card imageSylow := by
        have hrel := Subgroup.relIndex_ker (K := (sylow : Subgroup K))
          conjugation.rangeRestrict
        rw [MonoidHom.ker_rangeRestrict, hker] at hrel
        exact hrel
      rw [hindex] at hmul
      have hpos : 0 < Nat.card A := Nat.card_pos
      nlinarith
  rw [← hfactor]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (Nat.card A) himage
