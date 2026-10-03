module

public import Theory.Character.ModularBlock.BrauerCharacterBasis
public import Theory.Representation.CoefficientReduction

/-!
# Brauer values of integral matrix representations

For a representation over the localization of the chosen cyclotomic order,
its complex character and the genuine Brauer value of its reduction agree
at every odd-order element. No irreducibility or block-membership hypothesis
is needed.

Every complex eigenvalue is a group-order root of unity, hence belongs to the
cyclotomic order. The complex characteristic polynomial therefore factors
using roots in that order, with their integer algebraic multiplicities.
Injectivity of the localization embedding descends this factorization;
coefficient reduction then gives the modular root multiset. Uniqueness of
odd-order lifts at the actual prime identifies each lifted root with the
original root, and taking sums proves the character identity.

This is the eigenvalue comparison in integral lattice reduction; see Serre,
*Linear Representations of Finite Groups*, Chapter 15. The definitions of the
prime and of genuine Brauer values are those of `BrauerCoefficientExtension`
and `BrauerCharacterBasis`.
-/

public section
noncomputable section

open Polynomial

namespace ModularBlock.BrauerCharacter

open PrincipalBlockConstruction BrauerCoefficientExtension

variable {G : Type*} [Group G] [Finite G]
variable (d : PrincipalCongruenceBlockData G)

private theorem complex_roots_in_order {m : ℕ}
    (ρ : Representation ℂ G (Fin m → ℂ)) (g : G) :
    ∃ roots : Multiset (cyclotomicOrder d.eta),
      roots.map (cyclotomicOrder d.eta).subtype = (ρ g).charpoly.roots ∧
      ∀ a ∈ roots, a ^ orderOf g = 1 := by
  classical
  have hpow (x : ℂ) (hx : x ∈ (ρ g).charpoly.roots) : x ^ orderOf g = 1 := by
    apply Representation.eigenvalue_pow_eq_one_of_pow_eq_one
      (f := ρ g) (by rw [← map_pow, pow_orderOf_eq_one, map_one])
    exact (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
      ((Polynomial.mem_roots (LinearMap.charpoly_monic _).ne_zero).mp hx)
  have hmem (x : ℂ) (hx : x ∈ (ρ g).charpoly.roots) : x ∈ cyclotomicOrder d.eta := by
    have hcard : x ^ Nat.card G = 1 := by
      obtain ⟨k, hk⟩ := orderOf_dvd_natCard g
      rw [hk, pow_mul, hpow x hx, one_pow]
    let : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
    obtain ⟨i, _, hi⟩ := d.eta_spec.eq_pow_of_pow_eq_one hcard
    rw [← hi]
    exact pow_mem_cyclotomicOrder (eta_mem_cyclotomicOrder d.eta) i
  let lift : {x // x ∈ (ρ g).charpoly.roots} → cyclotomicOrder d.eta :=
    fun x => ⟨x.1, hmem x.1 x.2⟩
  refine ⟨(ρ g).charpoly.roots.attach.map lift, ?_, ?_⟩
  · simpa only [Multiset.map_map, Function.comp_def, lift, Subring.subtype_apply] using
      (ρ g).charpoly.roots.attach_map_val
  · intro a ha
    obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp ha
    apply Subtype.ext
    exact hpow x.1 x.2

private theorem localized_charpoly_factorization {m : ℕ}
    (σ : Representation (Localization.AtPrime d.primeIdeal) G
      (Fin m → Localization.AtPrime d.primeIdeal)) (g : G)
    (roots : Multiset (cyclotomicOrder d.eta))
    (hroots : roots.map (cyclotomicOrder d.eta).subtype =
      (Representation.mapCoefficients (BlockOrthogonality.localizationToComplex d.primeIdeal)
        σ g).charpoly.roots) :
    (σ g).charpoly =
      (roots.map (fun a => X - C (algebraMap _ (Localization.AtPrime d.primeIdeal) a))).prod := by
  apply Polynomial.map_injective (BlockOrthogonality.localizationToComplex d.primeIdeal)
    (BlockOrthogonality.localizationToComplex_injective d)
  rw [← Representation.mapCoefficients_charpoly]
  rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (LinearMap.charpoly_monic _), ← hroots]
  simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, BlockOrthogonality.localizationToComplex_algebraMap,
    Subring.subtype_apply]

/-- Integral reduction preserves the characteristic-zero eigenvalue sum at odd-order elements. -/
theorem character_eq_value_mapCoefficients {m : ℕ}
    (σ : Representation (Localization.AtPrime d.primeIdeal) G
      (Fin m → Localization.AtPrime d.primeIdeal)) (g : G) (hg : Odd (orderOf g)) :
    (Representation.mapCoefficients (BlockOrthogonality.localizationToComplex d.primeIdeal)
      σ).character g = value d (Representation.mapCoefficients (localizedReduction d) σ) g := by
  classical
  obtain ⟨roots, hcomplex, hpow⟩ := complex_roots_in_order d
    (Representation.mapCoefficients (BlockOrthogonality.localizationToComplex d.primeIdeal) σ) g
  have hfactor := localized_charpoly_factorization d σ g roots hcomplex
  have hmodular : (Representation.mapCoefficients (localizedReduction d) σ g).charpoly.roots =
      roots.map (reduction d) := by
    rw [Representation.mapCoefficients_charpoly, hfactor]
    have heq : ((roots.map (fun a => X - C
        (algebraMap _ (Localization.AtPrime d.primeIdeal) a))).prod).map (localizedReduction d) =
        ((roots.map (reduction d)).map (fun a => X - C a)).prod := by
      simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.map_sub,
        Polynomial.map_X, Polynomial.map_C, localizedReduction_algebraMap]
    rw [heq, Polynomial.roots_multiset_prod_X_sub_C]
  have hlift : (roots.map (reduction d)).map (eigenvalueLift d) = roots := by
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id roots]
    apply Multiset.map_congr rfl
    intro a ha
    have haPow : reduction d a ^ orderOf g = 1 := by rw [← map_pow, hpow a ha, map_one]
    rw [Function.comp_apply, eigenvalueLift_eq_liftAtOrder d (orderOf g) hg
      (orderOf_dvd_natCard g) _ haPow]
    apply odd_root_eq_of_reduction_eq d hg hg (orderOf_dvd_natCard g)
      (orderOf_dvd_natCard g) (liftAtOrder_pow _ _ _ _ _ _) (hpow a ha)
    exact reduction_liftAtOrder _ _ _ _ _ _
  rw [value, integralValue, hmodular, hlift]
  change LinearMap.trace ℂ (Fin m → ℂ) _ = _
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _), ← hcomplex]
  exact (map_multiset_sum (cyclotomicOrder d.eta).subtype roots).symm

end ModularBlock.BrauerCharacter
