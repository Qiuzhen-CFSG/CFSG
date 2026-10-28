module

public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.SylowNormalization
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.KernelNormalizer
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.Representatives
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.RepresentativeGeneration

/-!
# Coverage of proper Tits subgroups with order divisible by 25

Two independent certificates suffice: coverage by the 25 max8 and seven max4
double-coset candidates, and generator recovery for their nonidentity rows.
The max4 rows exclude every strict proper overgroup of max4. The max8 rows
show that two distinct marked five-kernels generate a subgroup containing a
conjugate of max4. Normalization by max8 transports that assertion through
the double-coset factors. Sylow conjugacy then gives exactly the max4/max8
placement required by the minimum-index assembly.

The unconditional `coverage` theorem assembles all four kernel-checked finite
certificates with Sylow normalization. It places every proper subgroup whose
order is divisible by 25 in a conjugate of the literal max4 or max8 candidate,
without any candidate-order or maximal-subgroup-catalogue premise.

Source: the primary ATLAS Tits entry and its unmodified max4/max8 programs,
recorded in `MinimumIndex/source/`. Reproducible candidate exploration is in
`FiveOvergroups/source/`. This module does not import the minimum-index assembly.
-/

namespace Tits.MinimumIndexFiveOvergroups
open Subgroup MinimumIndexCandidates FiveFrobenius

private theorem conj_map_map (H : Subgroup Atlas1600Group) (g h : Atlas1600Group) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      H.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

private theorem conj_map_inv (H : Subgroup Atlas1600Group) (g : Atlas1600Group) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [conj_map_map, inv_mul_cancel]
  change H.map (MonoidHom.id _) = H
  exact Subgroup.map_id H

private theorem conj_ne_top (H : Subgroup Atlas1600Group) (hH : H ≠ ⊤)
    (g : Atlas1600Group) : H.map (MulAut.conj g).toMonoidHom ≠ ⊤ := by
  intro he
  have h := congrArg (fun K : Subgroup Atlas1600Group =>
    K.map (MulAut.conj g⁻¹).toMonoidHom) he
  rw [conj_map_inv, Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective] at h
  exact hH h

/-- Exhaustive max4 double cosets and six generator-recovery certificates
exclude a strict proper overgroup of the literal max4 candidate. -/
public theorem max4_eq_of_certificates
    (hcover : ∀ x : Atlas1600Group, ∃ (a b : max4) (i : Fin 7),
      x = a.val * max4Rep i * b.val)
    (hgenerate : ∀ i : Fin 7, i ≠ 0 → max4 ⊔ closure {max4Rep i} = ⊤)
    (H : Subgroup Atlas1600Group) (hM : max4 ≤ H) (hH : H ≠ ⊤) : H = max4 := by
  classical
  apply le_antisymm ?_ hM
  intro x hx
  obtain ⟨a, b, i, he⟩ := hcover x
  by_cases hi : i = 0
  · rw [he, hi, max4Rep_zero, mul_one]
    exact max4.mul_mem a.property b.property
  have hr : max4Rep i ∈ H := by
    have hm := H.mul_mem (H.mul_mem (H.inv_mem (hM a.property)) hx)
      (H.inv_mem (hM b.property))
    have heq : a.val⁻¹ * x * b.val⁻¹ = max4Rep i := by rw [he]; group
    rwa [heq] at hm
  have hle : max4 ⊔ closure {max4Rep i} ≤ H :=
    sup_le hM ((closure_le _).mpr (by rintro y (rfl : y = max4Rep i); exact hr))
  rw [hgenerate i hi] at hle
  exact False.elim (hH (top_unique hle))

private theorem kernel_conj_eq (a : max8) :
    kernel.map (MulAut.conj a.val).toMonoidHom = kernel :=
  mem_normalizer_iff_map_conj_eq.mp (max8_normalizes_kernel a.property)

/-- A max8 double-coset cover reduces generation by two five-kernels to the
24 nonidentity rows. Both double-coset factors are handled by the proved
normalization in the actual carrier. -/
public theorem pair_generation_of_certificates
    (hcover : ∀ x : Atlas1600Group, ∃ (a b : max8) (i : Fin 25),
      x = a.val * max8Rep i * b.val)
    (hgenerate : ∀ i : Fin 25, i ≠ 0 → ∃ g : Atlas1600Group,
      max4.map (MulAut.conj g).toMonoidHom ≤
        kernel ⊔ kernel.map (MulAut.conj (max8Rep i)).toMonoidHom)
    (x : Atlas1600Group) (hx : x ∉ max8) : ∃ g : Atlas1600Group,
      max4.map (MulAut.conj g).toMonoidHom ≤
        kernel ⊔ kernel.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨a, b, i, he⟩ := hcover x
  have hi : i ≠ 0 := by
    intro hi
    apply hx
    rw [he, hi, max8Rep_zero, mul_one]
    exact max8.mul_mem a.property b.property
  obtain ⟨g, hg⟩ := hgenerate i hi
  have heq : kernel.map (MulAut.conj x).toMonoidHom =
      (kernel.map (MulAut.conj (max8Rep i)).toMonoidHom).map
        (MulAut.conj a.val).toMonoidHom := by
    rw [he, ← conj_map_map kernel b.val (a.val * max8Rep i), kernel_conj_eq b,
      conj_map_map]
  have hm := Subgroup.map_mono (f := (MulAut.conj a.val).toMonoidHom) hg
  rw [conj_map_map] at hm
  rw [Subgroup.map_sup, kernel_conj_eq a, ← heq] at hm
  exact ⟨a.val * g, hm⟩

/-- The two independent inputs concern generation by two actual five-subgroups
and maximality of the actual max4 candidate. They remain explicit. -/
private theorem marked_coverage_of_pair_generation
    (hmax : ∀ H : Subgroup Atlas1600Group,
      MinimumIndexCandidates.max4 ≤ H → H ≠ ⊤ → H = MinimumIndexCandidates.max4)
    (hpair : ∀ x : Atlas1600Group, x ∉ MinimumIndexCandidates.max8 →
      ∃ g : Atlas1600Group,
        MinimumIndexCandidates.max4.map (MulAut.conj g).toMonoidHom ≤
          FiveFrobenius.kernel ⊔ FiveFrobenius.kernel.map (MulAut.conj x).toMonoidHom)
    (H : Subgroup Atlas1600Group) (hH : H ≠ ⊤) (hP : FiveFrobenius.kernel ≤ H) :
    ∃ g : Atlas1600Group,
      H.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max4 ∨
      H.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max8 := by
  classical
  by_cases hN : H ≤ MinimumIndexCandidates.max8
  · refine ⟨1, Or.inr ?_⟩
    change H.map (MonoidHom.id _) ≤ _
    rwa [Subgroup.map_id]
  obtain ⟨x, hx, hxN⟩ := SetLike.not_le_iff_exists.mp hN
  obtain ⟨g, hg⟩ := hpair x hxN
  have hPx : FiveFrobenius.kernel.map (MulAut.conj x).toMonoidHom ≤ H := by
    rintro y ⟨z, hz, rfl⟩
    exact H.mul_mem (H.mul_mem hx (hP hz)) (H.inv_mem hx)
  have hM := hg.trans (sup_le hP hPx)
  have hM' : MinimumIndexCandidates.max4 ≤ H.map (MulAut.conj g⁻¹).toMonoidHom := by
    have hm := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hM
    rwa [conj_map_inv] at hm
  exact ⟨g⁻¹, Or.inl (hmax _ hM' (conj_ne_top H hH _)).le⟩

/-- Literal candidate coverage follows from the two five-subgroup generation
certificate and max4 maximality. Sylow normalization is fully discharged. -/
public theorem coverage_of_pair_generation
    (hmax : ∀ H : Subgroup Atlas1600Group,
      MinimumIndexCandidates.max4 ≤ H → H ≠ ⊤ → H = MinimumIndexCandidates.max4)
    (hpair : ∀ x : Atlas1600Group, x ∉ MinimumIndexCandidates.max8 →
      ∃ g : Atlas1600Group,
        MinimumIndexCandidates.max4.map (MulAut.conj g).toMonoidHom ≤
          FiveFrobenius.kernel ⊔ FiveFrobenius.kernel.map (MulAut.conj x).toMonoidHom)
    (L : Subgroup Atlas1600Group) (hL : L ≠ ⊤) (h25 : 25 ∣ Nat.card L) :
    ∃ g : Atlas1600Group,
      L.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max4 ∨
      L.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max8 := by
  obtain ⟨g, hg⟩ := exists_conjugate_contains_kernel L h25
  obtain ⟨h, hh⟩ := marked_coverage_of_pair_generation hmax hpair
    (L.map (MulAut.conj g).toMonoidHom) (conj_ne_top L hL g) hg
  exact ⟨h * g, by simpa only [conj_map_map] using hh⟩

/-- This is the exact five-overgroup input to the minimum-index assembly,
conditional only on the two independent finite certificate families. -/
public theorem coverage_of_certificates
    (hcover8 : ∀ x : Atlas1600Group, ∃ (a b : max8) (i : Fin 25),
      x = a.val * max8Rep i * b.val)
    (hcover4 : ∀ x : Atlas1600Group, ∃ (a b : max4) (i : Fin 7),
      x = a.val * max4Rep i * b.val)
    (hgenerate8 : ∀ i : Fin 25, i ≠ 0 → ∃ g : Atlas1600Group,
      max4.map (MulAut.conj g).toMonoidHom ≤
        kernel ⊔ kernel.map (MulAut.conj (max8Rep i)).toMonoidHom)
    (hgenerate4 : ∀ i : Fin 7, i ≠ 0 → max4 ⊔ closure {max4Rep i} = ⊤)
    (L : Subgroup Atlas1600Group) (hL : L ≠ ⊤) (h25 : 25 ∣ Nat.card L) :
    ∃ g : Atlas1600Group,
      L.map (MulAut.conj g).toMonoidHom ≤ max4 ∨
      L.map (MulAut.conj g).toMonoidHom ≤ max8 :=
  coverage_of_pair_generation (max4_eq_of_certificates hcover4 hgenerate4)
    (pair_generation_of_certificates hcover8 hgenerate8) L hL h25

/-- Every proper subgroup of the actual Tits carrier whose order is divisible
by 25 is conjugate into the literal ATLAS max4 or max8 candidate. This supplies
the `hfive` input of `atlas1600_subgroup_index_ge_of_candidate_coverage`, with
all four finite certificate premises discharged. -/
public theorem coverage
    (L : Subgroup Atlas1600Group) (hL : L ≠ ⊤) (h25 : 25 ∣ Nat.card L) :
    ∃ g : Atlas1600Group,
      L.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max4 ∨
      L.map (MulAut.conj g).toMonoidHom ≤ MinimumIndexCandidates.max8 :=
  coverage_of_certificates max8_doubleCoset_cover max4_doubleCoset_cover
    max8_pair_generates max4_rep_generates L hL h25

end Tits.MinimumIndexFiveOvergroups
