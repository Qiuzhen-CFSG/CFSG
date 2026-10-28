module
public import Theory.Representation.BinaryConjugationSection
public import Theory.SpecificGroups.SL2.OddFixedVectors
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Odd fixed points in a natural binary section

A nontrivial odd subgroup of a covering actor survives its two-group kernel.
Its natural matrix action fixes no nonzero vector. Thus, when the subgroup
centralizes the coordinate kernel, its fixed subgroup on the entire original
numerator is exactly that kernel. No splitting of the central extension is
assumed. The literal path-torus application is DGS 9.8, pp.145--146, in
CommutingTrivial.DistanceThreeTorus.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G]

/-- A nontrivial odd actor fixes exactly the retained kernel of a natural
section, provided it centralizes that kernel. -/
theorem natural_odd_fixed_eq_kernel
    (H A Z₀ : Subgroup G) {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
    (q : H →* SL(2,F)) (hp : IsPGroup 2 q.ker)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) SL(2,F) W)
    (c : BinaryConjugationSection H A Z₀ (σ.comp q))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (hE : ∀ g z, E (σ g z) = Matrix.mulVec g.val (E z))
    (D : Subgroup G) (hDH : D ≤ H) (ho : Odd (Nat.card D)) (hne : D ≠ ⊥)
    (hcD : Z₀ ≤ centralizer (D : Set G)) :
    A ⊓ centralizer (D : Set G) = Z₀ := by
  obtain ⟨d,hd,hdne⟩ := D.bot_or_exists_ne_one.resolve_left hne
  let k : H := ⟨d,hDH hd⟩
  have hodd : Odd (orderOf k) := by
    rw [Subgroup.orderOf_mk]
    apply ho.of_dvd_nat
    simpa only [Subgroup.orderOf_mk] using _root_.orderOf_dvd_natCard (⟨d,hd⟩ : D)
  have hkn : q k ≠ 1 := by
    intro hh
    have hc := hp.orderOf_coprime hodd.coprime_two_left (⟨k,hh⟩ : q.ker)
    have he : orderOf (⟨k,hh⟩ : q.ker) = orderOf k :=
      Subgroup.orderOf_mk (H := q.ker) k hh
    rw [he] at hc
    have hc' : Nat.Coprime (orderOf d) (orderOf d) := by
      simpa only [k,Subgroup.orderOf_mk] using hc
    exact hdne (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc' dvd_rfl dvd_rfl))
  apply le_antisymm ?_ (le_inf c.kernel_le hcD)
  rintro z ⟨hz,hfix⟩
  let zA : A := ⟨z,hz⟩
  have hconj : (⟨(k : G)*z*(k : G)⁻¹,
      (mem_normalizer_iff.mp (c.normalized k.property) z).mp zA.property⟩ : A) = zA := by
    apply Subtype.ext
    change d*z*d⁻¹=z
    rw [hfix d hd,mul_inv_cancel_right]
  have heq : σ (q k) (c.coordinates zA).toAdd = (c.coordinates zA).toAdd :=
    (c.equivariant k zA).symm.trans (congrArg (fun x => (c.coordinates x).toAdd) hconj)
  have hz0 : E (c.coordinates zA).toAdd = 0 :=
    Matrix.SL2.odd_power_fixed_eq_zero (q k) (orderOf k) hodd
      (by rw [←map_pow,pow_orderOf_eq_one,map_one]) hkn _ (by rw [←hE,heq])
  exact (c.coordinates_eq_one_iff zA).mp (E.injective (hz0.trans (map_zero E).symm))

end Representation.BinaryConjugationSection
