module
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SevenSylowOvergroups
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ThreeSylowContainment
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.InvolutionCentralizer
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import Theory.AtlasPort.LinearGroups.G2.ExceptionalLocalQuotients.Numbering
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines
public import Theory.GroupTheory.SolvableSylowControl.Marked

/-!
# Maximal Sylow-center centralizers in G₂(2)′

A proper overgroup of the marked Sylow subgroup has order prime to seven.
The existing solvable-overgroup argument also excludes nine. Consequently
any such overgroup of either order-96 parabolic has that same order, proving
maximality. The full Sylow-center computation identifies its centralizer
with the first parabolic, retaining the order-four central elements.
Sylow conjugacy transports maximality along an actual group equivalence.

This supplies the intrinsic maximality used by the original ordinary
15.1.20(3c) row. Source: Aschbacher--Smith, printed pp.1095--1096.
The octonion carrier and checked root-word calculations are inherited
from the licensed ATLAS port; see LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Theory.GroupTheory
namespace Atlas.G2.BinarySylowCenterMaximal
open BinaryParabolicPair

private theorem derived_card : Nat.card DerivedModel = 6048 := by
  rw [DerivedModel,commutator_eq_longRootClosure]
  exact BinaryException.card_H

private theorem proper_overgroup_card (H : Subgroup DerivedModel) (hH : H ≠ ⊤)
    (hSH : (derivedSylow : Subgroup DerivedModel) ≤ H) (hc : 96 ∣ Nat.card H) :
    Nat.card H = 96 := by
  let : IsSimpleGroup DerivedModel := isSimple_commutator_binary
  have h7 : ¬ 7 ∣ Nat.card H := fun hd =>
    hH (SevenSylowOvergroups.eq_top_of_seven_dvd H hSH hd)
  have hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3 := by
    intro p hp hd
    have hdiv : Nat.card H ∣ 6048 := by
      simpa only [derived_card] using H.card_subgroup_dvd_card
    have hd' : p ∣ 2^5 * 3^3 * 7 := hd.trans hdiv
    rcases hp.dvd_mul.mp hd' with h23 | hd7
    · rcases hp.dvd_mul.mp h23 with hd2 | hd3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow hd2))
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
          (hp.dvd_of_dvd_pow hd3))
    · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp hd7
      exact (h7 (he ▸ hd)).elim
  have h9 := ThreeSylowContainment.nine_not_dvd_card_of_sylow_le H hH
    (isSolvable_of_prime_dvd_card_eq_two_or_three H hprimes) hSH hprimes
  obtain ⟨k,hk⟩ := hc
  have hk63 : k ∣ 63 := by
    apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 96)).mp
    have hd := H.card_subgroup_dvd_card
    rw [derived_card,hk] at hd
    exact hd
  have hkcases : k = 1 ∨ k = 3 ∨ k = 7 ∨ k = 9 ∨ k = 21 ∨ k = 63 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 63) hk63
    exact (by decide +kernel : ∀ j : Fin 64, j.val ∣ 63 →
      j.val = 1 ∨ j.val = 3 ∨ j.val = 7 ∨ j.val = 9 ∨ j.val = 21 ∨ j.val = 63)
        ⟨k,by omega⟩ hk63
  rcases hkcases with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using hk
  · exact (h9 (by rw [hk]; decide)).elim
  · exact (h7 (by rw [hk]; decide)).elim
  · exact (h9 (by rw [hk]; decide)).elim
  · exact (h7 (by rw [hk]; decide)).elim
  · exact (h7 (by rw [hk]; decide)).elim

/-- Both order-96 parabolics of the actual binary derived G₂ are maximal. -/
theorem parabolic_isCoatom (P : Subgroup DerivedModel)
    (hSP : (derivedSylow : Subgroup DerivedModel) ≤ P) (hc : Nat.card P = 96) :
    IsCoatom P := by
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨?_,fun H hH hPH => ?_⟩
  · intro he
    rw [he,card_top,derived_card] at hc
    omega
  · have hcard := proper_overgroup_card H hH (hSP.trans hPH)
      (hc ▸ card_dvd_of_le hPH)
    exact (eq_of_le_of_card_ge hPH (by rw [hc,hcard])).ge

/-- The first parabolic centralizes the full center, including its order-four elements. -/
theorem standard_centralizer :
    centralizer ((center derivedSylow).map (derivedSylow : Subgroup DerivedModel).subtype :
      Set DerivedModel) = derivedFirst := by
  apply le_antisymm
  · rw [← centralizer_derivedInvolution_eq_first]
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    have hz : (⟨derivedInvolution,derivedInvolution_mem_sylow⟩ : derivedSylow) ∈
        center derivedSylow := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp
        (centralizer_derivedInvolution_eq_first.symm ▸ derivedSylow_le_first y.property)
    exact (hx derivedInvolution (mem_map_of_mem _ hz)).symm
  · intro x hx z hz
    obtain ⟨w,hw,rfl⟩ := hz
    exact ExceptionalLocalQuotients.derivedFirst_centralizes_sylow_center ⟨w,hw⟩ ⟨x,hx⟩

private theorem centralizer_map_equiv {K H : Type*} [Group K] [Group H]
    (e : K ≃* H) (Z : Subgroup K) :
    (centralizer (Z : Set K)).map e.toMonoidHom = centralizer (Z.map e.toMonoidHom : Set H) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro z hz
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e z) (mem_map_of_mem _ hz)

/-- The centralizer of the full center of any Sylow is maximal in every actual model. -/
theorem centralizer_isCoatom {K : Type*} [Group K]
    (e : K ≃* DerivedModel) (S : Sylow 2 K) :
    IsCoatom (centralizer ((center S).map (S : Subgroup K).subtype : Set K)) := by
  let : Finite K := Finite.of_injective e e.injective
  obtain ⟨_,f,_,hf⟩ := SolvableSylowControl.exists_aligned_equiv e S derivedSylow
  have hZ : ((center S).map (S : Subgroup K).subtype).map f.toMonoidHom =
      (center derivedSylow).map (derivedSylow : Subgroup DerivedModel).subtype := by
    rw [map_map, ← map_center_image_of_injective (S : Subgroup K) f.toMonoidHom f.injective, hf]
  apply (f.mapSubgroup.isCoatom_iff _).mp
  change IsCoatom ((centralizer ((center S).map (S : Subgroup K).subtype : Set K)).map f.toMonoidHom)
  rw [centralizer_map_equiv,hZ,standard_centralizer]
  exact parabolic_isCoatom derivedFirst derivedSylow_le_first card_derivedFirst

end Atlas.G2.BinarySylowCenterMaximal
