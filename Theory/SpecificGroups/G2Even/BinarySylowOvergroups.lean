module

public import Theory.SpecificGroups.G2Even.BinarySylowCenterMaximal
public import Theory.AtlasPort.LinearGroups.G2.DerivedNormalizerSolvable.Binary

/-!
# Proper Sylow overgroups in the actual binary derived G₂ group

A proper subgroup containing the marked Sylow two-subgroup has no factor
seven in its order, by the actual seven-point generation calculation, and
no factor nine, by the checked local geometry. Hence a strict Sylow
overgroup has order 96 and is maximal. Sylow conjugacy transports this
fact and the full Sylow normalizer to any actual G₂(2)′ model.

The consumer is the original ordinary 15.1.22(4) component: cubic residual
escape makes M ∩ L strictly larger than its Sylow subgroup. No parabolic
placement, exchanged plane or extra model hypothesis is needed.
Source: Aschbacher--Smith, printed pp.1098--1099, refs/quasithin.pdf.
The underlying octonion calculations come from the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Theory.GroupTheory

namespace Atlas.G2.BinarySylowOvergroups
open BinaryParabolicPair


theorem overgroup_isCoatom (H : Subgroup DerivedModel) (hH : H ≠ ⊤)
    (hS : (derivedSylow : Subgroup DerivedModel) < H) : IsCoatom H := by
  let : IsSimpleGroup DerivedModel := isSimple_commutator_binary
  have hcD : Nat.card DerivedModel = 6048 := by
    rw [DerivedModel,commutator_eq_longRootClosure]
    exact BinaryException.card_H
  have h7 : ¬ 7 ∣ Nat.card H := fun hd =>
    hH (SevenSylowOvergroups.eq_top_of_seven_dvd H hS.le hd)
  have hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3 := by
    intro p hp hd
    have hd' : p ∣ 2^5 * 3^3 * 7 := by
      change p ∣ 6048
      simpa only [hcD] using hd.trans H.card_subgroup_dvd_card
    rcases hp.dvd_mul.mp hd' with h23 | hd7
    · rcases hp.dvd_mul.mp h23 with hd2 | hd3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow hd2))
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
          (hp.dvd_of_dvd_pow hd3))
    · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp hd7
      exact (h7 (he ▸ hd)).elim
  have h9 := ThreeSylowContainment.nine_not_dvd_card_of_sylow_le H hH
    (isSolvable_of_prime_dvd_card_eq_two_or_three H hprimes) hS.le hprimes
  have h32 : 32 ∣ Nat.card H := card_derivedSylow ▸ card_dvd_of_le hS.le
  obtain ⟨k,hk⟩ := h32
  have hk189 : k ∣ 189 := by
    apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 32)).mp
    have hd := H.card_subgroup_dvd_card
    rw [hcD,hk] at hd
    exact hd
  have hkc : k = 1 ∨ k = 3 ∨ k = 7 ∨ k = 9 ∨ k = 21 ∨ k = 27 ∨ k = 63 ∨ k = 189 := by
    have hb := Nat.le_of_dvd (by decide : 0 < 189) hk189
    exact (by decide +kernel : ∀ j : Fin 190, j.val ∣ 189 →
      j.val = 1 ∨ j.val = 3 ∨ j.val = 7 ∨ j.val = 9 ∨ j.val = 21 ∨
      j.val = 27 ∨ j.val = 63 ∨ j.val = 189) ⟨k,by omega⟩ hk189
  have hc : Nat.card H = 96 := by
    rcases hkc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hS.ne (eq_of_le_of_card_ge hS.le (by rw [card_derivedSylow,hk]))).elim
    · exact hk
    · exact (h7 (by rw [hk]; decide)).elim
    · exact (h9 (by rw [hk]; decide)).elim
    · exact (h7 (by rw [hk]; decide)).elim
    · exact (h9 (by rw [hk]; decide)).elim
    · exact (h7 (by rw [hk]; decide)).elim
    · exact (h7 (by rw [hk]; decide)).elim
  exact BinarySylowCenterMaximal.parabolic_isCoatom H hS.le hc
end Atlas.G2.BinarySylowOvergroups

namespace Atlas.G2.BinarySylowOvergroups
open BinaryParabolicPair

/-- Maximality and the full Sylow normalizer for the caller's actual G₂(2)′ model. -/
theorem sylow_geometry {K : Type*} [Group K]
    (e : K ≃* DerivedModel) (P : Sylow 2 K) :
    normalizer (P : Set K) = P ∧
      IsCoatom (centralizer ((center P).map (P : Subgroup K).subtype : Set K)) ∧
      ∀ H : Subgroup K, H ≠ ⊤ → (P : Subgroup K) ≤ H →
        ¬ H ≤ centralizer ((center P).map (P : Subgroup K).subtype : Set K) → IsCoatom H := by
  let : Finite K := Finite.of_injective e e.injective
  obtain ⟨_,f,_,hf⟩ := SolvableSylowControl.exists_aligned_equiv e P derivedSylow
  refine ⟨?_, BinarySylowCenterMaximal.centralizer_isCoatom e P, ?_⟩
  · apply map_injective (f := f.toMonoidHom) f.injective
    calc
      _ = normalizer (((P : Subgroup K).map f.toMonoidHom) : Set DerivedModel) :=
        map_equiv_normalizer_eq (P : Subgroup K) f
      _ = _ := by
        rw [hf]
        exact DerivedNormalizerSolvable.binary_normalizer_derivedSylow
  · intro H hH hPH hout
    apply (f.mapSubgroup.isCoatom_iff H).mp
    apply overgroup_isCoatom
    · intro he
      apply hH
      apply map_injective (f := f.toMonoidHom) f.injective
      change H.map f.toMonoidHom = ⊤ at he
      exact he.trans (map_top_of_surjective f.toMonoidHom f.surjective).symm
    · rw [← hf]
      apply (f.mapSubgroup.lt_iff_lt).mpr
      apply lt_of_le_of_ne hPH
      intro he
      apply hout
      rw [← he]
      rintro x hx _ ⟨z,hz,rfl⟩
      exact (congrArg Subtype.val (mem_center_iff.mp hz ⟨x,hx⟩)).symm
end Atlas.G2.BinarySylowOvergroups
