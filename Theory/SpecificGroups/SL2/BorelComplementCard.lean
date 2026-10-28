module
public import Theory.SpecificGroups.SL2.TwoCoreBorel
/-!
# Recognizing a Borel complement from its order

In characteristic two the Borel quotient by its Sylow two subgroup is the
multiplicative group of the field. A disjoint subgroup of order |F|−1
maps injectively onto that quotient, hence surjectively by equal cardinality.
It therefore supplements the original Sylow subgroup in its normalizer.

This recovers the literal quotient complement used in the Hall-torus
automorphism step of Aschbacher–Smith 2.4.8(5), printed p.530.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {A F : Type*} [Group A] [Finite A] [Field F] [Finite F] [CharP F 2]

theorem sylow_normalizer_complement_of_card
    (q : A →* SL(2,F)) (hq : Function.Surjective q) (P : Sylow 2 A)
    (hk : q.ker ≤ (P : Subgroup A)) (D : Subgroup A)
    (hDN : D ≤ normalizer (P : Set A)) (hd : Disjoint (P : Subgroup A) D)
    (hcard : Nat.card D = Nat.card F - 1) :
    (P : Subgroup A) ⊔ D = normalizer (P : Set A) := by
  obtain ⟨f,hf,hker⟩ := exists_sylowNormalizer_diagonal q hq P hk
  let N := normalizer (P : Set A)
  let r : D →* Fˣ := f.comp (inclusion hDN)
  have hr : Function.Injective r := by
    apply (MonoidHom.ker_eq_bot_iff r).mp
    apply eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    exact disjoint_def.mp hd ((hker (inclusion hDN x)).mp hx) x.property
  have hrs : Function.Surjective r := (Nat.bijective_iff_injective_and_card r).mpr
    ⟨hr,by rw [Nat.card_units];exact hcard⟩ |>.2
  apply le_antisymm (sup_le (P : Subgroup A).le_normalizer hDN)
  intro y hy
  obtain ⟨d,hd⟩ := hrs (f ⟨y,hy⟩)
  have hdiff : y*(d:A)⁻¹ ∈ P := by
    apply (hker (⟨y,hy⟩ * (inclusion hDN d)⁻¹)).mp
    rw [map_mul,map_inv]
    change f ⟨y,hy⟩ * (r d)⁻¹=1
    rw [hd,mul_inv_cancel]
  have hh := mul_mem_sup hdiff d.property
  simpa only [inv_mul_cancel_right] using hh
end Matrix.SpecialLinearGroup

