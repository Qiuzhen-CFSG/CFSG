module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.QuotientGeometry
public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.CyclicTI
public import Theory.Representation.GoldschmidtONan.Consequences

/-!
# Excluding the singleton and swapped local alternatives

A normalizing cyclic TI conjugate commutes with the original actor, so a
noncommuting pair excludes a singleton orbit. For a two-member orbit, every
odd-order element preserves both members: its square lies in the stabilizer,
and its odd order recovers the element as a power of that square. Applying
this to the odd cyclic conjugate excludes the swapped alternative.

All normalizations are lifted through the actual quotient and subtype maps.
The source's swapping two-element is not replaced by an assumed involution.
These are local exclusions for Aschbacher–Smith E.6.24, printed p.255, using
GLS C.14.2 alternatives (i) and (ii).
-/

public section

open Module Subgroup Representation.BinaryOffender
namespace Representation.RegularCyclicNormalClosure
open FactorConstruction
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- Stabilizing the quotient fixed space forces normalization of the original actor. -/
theorem Input.normalizes_of_quotient_fixed_map (h : Input ρ C)
    (F : Submodule (ZMod 2) W) (hFU : F ≤ fixedSpace ρ C) (x : pointwiseFixer ρ F)
    (hx : (fixedSpace (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F))).map
      (quotientOnFixer ρ F x) =
        fixedSpace (quotientOnFixer ρ F) (C.subgroupOf (pointwiseFixer ρ F))) :
    C.map (MulAut.conj (x : A)).toMonoidHom = C := by
  rw [h.fixedSpace_quotientOnFixer F hFU, ← map_quotientOnFixer] at hx
  have hFx : F ≤ (fixedSpace ρ C).map (ρ (x : A)) :=
    (pointwiseFixer_map F x).ge.trans (Submodule.map_mono hFU)
  have hh := congrArg (fun L : Submodule (ZMod 2) (W ⧸ F) => L.comap F.mkQ) hx
  rw [Submodule.comap_map_mkQ, Submodule.comap_map_mkQ,
    sup_eq_right.mpr hFx, sup_eq_right.mpr hFU] at hh
  exact h.normal_in_stabilizer x hh

namespace FactorConstruction

/-- An odd-order actor cannot interchange the two members of a swapped orbit.
No involution is extracted from the source's swapping two-element. -/
theorem fixed_map_of_odd_order_of_swapped [Finite A]
    (h : GoldschmidtONan.Input ρ C) (hs : GoldschmidtONan.SwappedCase ρ C)
    (x : A) (hodd : Odd (orderOf x)) : (fixedSpace ρ C).map (ρ x) = fixedSpace ρ C := by
  let U := fixedSpace ρ C
  let S := displacementSpan ρ C ⊤
  let H := subspaceStabilizer ρ U
  have hUS : U ≠ S := h.fixed_ne_moved
  apply (GoldschmidtONan.mem_subspaceStabilizer_iff_map U x).mp
  have hsq : x ^ 2 ∈ H := by
    by_cases hx : U.map (ρ x) = U
    · exact H.pow_mem ((GoldschmidtONan.mem_subspaceStabilizer_iff_map U x).mpr hx) 2
    · have hxS : U.map (ρ x) = S := by
        have hm : U.map (ρ x) ∈ GoldschmidtONan.fixedOrbit ρ C := ⟨x, rfl⟩
        rw [hs.1] at hm
        exact (Set.mem_insert_iff.mp hm).resolve_left hx
      have hSorb : S ∈ GoldschmidtONan.fixedOrbit ρ C := by rw [hs.1]; exact Or.inr rfl
      have hSx := GoldschmidtONan.map_mem_fixedOrbit hSorb x
      rw [hs.1] at hSx
      have hxU : S.map (ρ x) = U := by
        rcases Set.mem_insert_iff.mp hSx with he | he
        · exact he
        · exact (hUS (GoldschmidtONan.orbit_map_injective x (hxS.trans he.symm))).elim
      apply (GoldschmidtONan.mem_subspaceStabilizer_iff_map U _).mpr
      rw [pow_two, GoldschmidtONan.orbit_map_mul, hxS, hxU]
  obtain ⟨k, hk⟩ := hodd
  have hp : (x ^ 2) ^ k * x = 1 := by
    rw [← pow_mul, ← pow_succ, ← hk]
    exact pow_orderOf_eq_one x
  have he : x = ((x ^ 2) ^ k)⁻¹ := by
    have hh := congrArg (fun g : A => ((x ^ 2) ^ k)⁻¹ * g) hp
    simpa only [← mul_assoc, inv_mul_cancel, one_mul, mul_one] using hh
  rw [he]
  exact H.inv_mem (H.pow_mem hsq k)

end FactorConstruction

variable [Finite A] [Finite W]

omit [Finite W] in
/-- A noncommuting conjugate contained in the local fixer excludes the singleton case. -/
theorem Input.not_singleton_onFixer (h : Input ρ C) (a : A)
    (hnc : ¬ ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d)
    (F : Submodule (ZMod 2) W) (hFU : F ≤ fixedSpace ρ C)
    (hDK : C.map (MulAut.conj a).toMonoidHom ≤ pointwiseFixer ρ F) :
    ¬ GoldschmidtONan.SingletonCase (quotientOnFixer ρ F)
      (C.subgroupOf (pointwiseFixer ρ F)) := by
  intro hs
  apply hnc
  apply h.commute_of_conjugate_le_normalizer a
  intro d hd
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact h.normalizes_of_quotient_fixed_map F hFU ⟨d, hDK hd⟩ (hs.2 ⟨d, hDK hd⟩)

/-- The odd cyclic conjugate acts trivially on a two-member orbit, excluding
GLS's swapped case for the local noncommuting pair. -/
theorem Input.not_swapped_onFixer (h : Input ρ C) (a : A)
    (hnc : ¬ ∀ c ∈ C, ∀ d ∈ C.map (MulAut.conj a).toMonoidHom, Commute c d)
    (F : Submodule (ZMod 2) W) (hFU : F ≤ fixedSpace ρ C)
    (hDK : C.map (MulAut.conj a).toMonoidHom ≤ pointwiseFixer ρ F)
    (hlocal : GoldschmidtONan.Input (quotientOnFixer ρ F)
      (C.subgroupOf (pointwiseFixer ρ F))) :
    ¬ GoldschmidtONan.SwappedCase (quotientOnFixer ρ F)
      (C.subgroupOf (pointwiseFixer ρ F)) := by
  intro hs
  apply hnc
  apply h.commute_of_conjugate_le_normalizer a
  intro d hd
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply h.normalizes_of_quotient_fixed_map F hFU ⟨d, hDK hd⟩
  apply fixed_map_of_odd_order_of_swapped hlocal hs
  have hcard : Nat.card (C.map (MulAut.conj a).toMonoidHom) = Nat.card C :=
    Subgroup.card_map_of_injective (MulAut.conj a).injective
  have hoddD : Odd (Nat.card (C.map (MulAut.conj a).toMonoidHom)) := hcard ▸ h.odd_card
  have ho := hoddD.of_dvd_nat (orderOf_dvd_natCard (⟨d, hd⟩ : C.map (MulAut.conj a).toMonoidHom))
  simpa only [← Subgroup.orderOf_coe] using ho

end Representation.RegularCyclicNormalClosure
