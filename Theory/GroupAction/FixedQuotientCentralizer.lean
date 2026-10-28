module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Centralizers detected by a fixed-point-free quotient action

Let D ≤ K normalize U. A homomorphism from U to a representation, whose
kernel is exactly C_U(K), identifies that representation with a quotient
of U. If the marked image of D fixes no nonzero vector, then C_U(D)=C_U(K).
The equivariance condition uses literal conjugation on U.

This is the quotient-to-subgroup step in Aschbacher–Smith,
Lemma 13.6.22, printed p.932 of the combined 1 March 2004 manuscript.
-/

public section
namespace Subgroup
variable {G A V : Type*} [Group G] [Group A]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- A fixed-point-free action on U/C_U(K) gives equality of the actual
centralizers in U. No splitting of U is assumed. -/
theorem inf_centralizer_eq_of_fixedFree_quotient
    (K U D : Subgroup G) (hDK : D ≤ K)
    (hKU : K ≤ normalizer (U : Set G))
    (ρ : Representation (ZMod 2) A V) (π : K →* A)
    (f : U →* Multiplicative V)
    (hker : f.ker = (centralizer (K : Set G)).subgroupOf U)
    (he : ∀ k : K, ∀ u : U,
      f (U.normalizerMonoidHom ⟨k, hKU k.property⟩ u) =
        Multiplicative.ofAdd (ρ (π k) (Multiplicative.toAdd (f u))))
    (hfree : ∀ w : V,
      (∀ d : D, ρ (π ⟨d, hDK d.property⟩) w = w) → w = 0) :
    U ⊓ centralizer (D : Set G) = U ⊓ centralizer (K : Set G) := by
  apply le_antisymm _ (inf_le_inf_left _ (centralizer_le hDK))
  rintro u ⟨hu, hc⟩
  refine ⟨hu, ?_⟩
  have hz : Multiplicative.toAdd (f ⟨u, hu⟩) = 0 := by
    apply hfree
    intro d
    have hfixed : U.normalizerMonoidHom ⟨(d : G), hKU (hDK d.property)⟩ ⟨u, hu⟩ =
        ⟨u, hu⟩ := by
      apply Subtype.ext
      change (d : G) * u * (d : G)⁻¹ = u
      rw [hc d d.property, mul_inv_cancel_right]
    have hh := he ⟨d, hDK d.property⟩ ⟨u, hu⟩
    rw [hfixed] at hh
    exact (congrArg Multiplicative.toAdd hh).symm
  have hm : (⟨u, hu⟩ : U) ∈ f.ker := hz
  rwa [hker] at hm

end Subgroup

namespace Representation
open Subgroup
variable {G A V : Type*} [Group G] [Group A]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- A chosen equivariant model of the literal quotient U/C_U(K).
The actor and quotient maps are part of the marking. No fixed-space or
incompatibility conclusion is a field. -/
structure ConjugationQuotientModel (K U : Subgroup G)
    (ρ : Representation (ZMod 2) A V) where
  normalizes : K ≤ normalizer (U : Set G)
  actor : K →* A
  quotient : U →* Multiplicative V
  surjective : Function.Surjective quotient
  kernel : quotient.ker = (centralizer (K : Set G)).subgroupOf U
  equivariant : ∀ k : K, ∀ u : U,
    quotient (U.normalizerMonoidHom ⟨k, normalizes k.property⟩ u) =
      Multiplicative.ofAdd (ρ (actor k) (Multiplicative.toAdd (quotient u)))

namespace ConjugationQuotientModel
variable {K U : Subgroup G} {ρ : Representation (ZMod 2) A V}

/-- The supplied surjection gives an actual quotient isomorphism; `kernel`
identifies its denominator with C_U(K). -/
noncomputable def quotientEquiv (m : ConjugationQuotientModel K U ρ) :
    U ⧸ m.quotient.ker ≃* Multiplicative V :=
  QuotientGroup.quotientKerEquivOfSurjective m.quotient m.surjective

/-- Use the chosen model to compare the actual ambient centralizers. -/
theorem centralizer_eq (m : ConjugationQuotientModel K U ρ)
    (D : Subgroup G) (hDK : D ≤ K)
    (hfree : ∀ w : V,
      (∀ d : D, ρ (m.actor ⟨d, hDK d.property⟩) w = w) → w = 0) :
    U ⊓ centralizer (D : Set G) = U ⊓ centralizer (K : Set G) :=
  inf_centralizer_eq_of_fixedFree_quotient K U D hDK m.normalizes ρ m.actor
    m.quotient m.kernel m.equivariant hfree
end ConjugationQuotientModel
end Representation
