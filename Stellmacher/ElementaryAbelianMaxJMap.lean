module

public import Stellmacher.ElementaryAbelianMaxJ

/-!
# Elementary Thompson subgroups under injective maps

An injective group homomorphism carries the maximal-order elementary
abelian subgroups of `S` exactly to those of the image of `S`.
Consequently it carries the elementary Thompson subgroup to the
elementary Thompson subgroup of that image.

The proof compares families using map and comap. Injectivity transports
elementary-abelianity back through a comap and preserves subgroup
cardinality. Every subgroup of the image is recovered from its comap,
so maximality transfers in both directions. Mapping the defining supremum
then proves the result.

This extends the automorphism transport API to subgroup subtype maps,
as needed to identify the intrinsic Baumann subgroup in the application
of (2.3) with the ambient `B₀` in Stellmacher (4.6).
Source: `refs/latex/stellmacher-n-group.tex`, second paragraph of (4.6).
-/

namespace Stellmacher

private theorem elementaryAbelian_comap_injective
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (B : Subgroup H)
    (hB : IsElementaryAbelian 2 B) : IsElementaryAbelian 2 (B.comap f) := by
  let _ : IsElementaryAbelian 2 B := hB
  refine {
    toIsMulCommutative := B.comap_injective_isMulCommutative hf
    exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  apply Subtype.ext
  apply hf
  simpa using elemPow_eq_one_of_isElementaryAbelian (p := 2) (f x) x.property

private theorem maxFamily_map_iff
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (S A : Subgroup G) :
    A.map f ∈ elementaryAbelianMaxSubgroups (S.map f) ↔
      A ∈ elementaryAbelianMaxSubgroups S := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · rintro ⟨hAS, hAe, hAmax⟩
    have hAelem : IsElementaryAbelian 2 A := by
      have hh := elementaryAbelian_comap_injective f hf (A.map f) hAe
      rwa [Subgroup.comap_map_eq_self_of_injective hf] at hh
    refine ⟨(Subgroup.map_le_map_iff_of_injective hf).mp hAS, hAelem, ?_⟩
    intro B hBS hBe
    have hh := hAmax (B.map f) (Subgroup.map_mono hBS) (hBe.map f)
    simpa only [Subgroup.card_map_of_injective hf] using hh
  · rintro ⟨hAS, hAe, hAmax⟩
    refine ⟨Subgroup.map_mono hAS, hAe.map f, ?_⟩
    intro B hBS hBe
    have hBrange : B ≤ f.range := hBS.trans (S.map_le_range f)
    have hBmap : (B.comap f).map f = B := Subgroup.map_comap_eq_self hBrange
    have hBpreS : B.comap f ≤ S := by
      apply (Subgroup.map_le_map_iff_of_injective hf).mp
      rwa [hBmap]
    have hh := hAmax (B.comap f) hBpreS (elementaryAbelian_comap_injective f hf B hBe)
    calc
      Nat.card B = Nat.card ((B.comap f).map f) :=
        congrArg (fun U : Subgroup H ↦ Nat.card U) hBmap.symm
      _ = Nat.card (B.comap f) := Subgroup.card_map_of_injective hf
      _ ≤ Nat.card A := hh
      _ = Nat.card (A.map f) := (Subgroup.card_map_of_injective hf).symm

/-- An injective homomorphism carries the elementary Thompson subgroup
to the elementary Thompson subgroup of the image. -/
public theorem elementaryAbelianMaxJ_map_injective
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (S : Subgroup G) :
    elementaryAbelianMaxJ (S.map f) = (elementaryAbelianMaxJ S).map f := by
  unfold elementaryAbelianMaxJ
  apply le_antisymm
  · apply sSup_le
    intro B hB
    have hBmap : (B.comap f).map f = B :=
      Subgroup.map_comap_eq_self (hB.1.trans (S.map_le_range f))
    have hA : B.comap f ∈ elementaryAbelianMaxSubgroups S := by
      apply (maxFamily_map_iff f hf S (B.comap f)).mp
      rwa [hBmap]
    rw [← hBmap]
    exact Subgroup.map_mono (le_sSup hA)
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply sSup_le
    intro A hA
    exact Subgroup.map_le_iff_le_comap.mp
      (le_sSup ((maxFamily_map_iff f hf S A).mpr hA))

end Stellmacher
