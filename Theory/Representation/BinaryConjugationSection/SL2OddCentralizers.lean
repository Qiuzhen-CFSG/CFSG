module
public import Theory.Representation.BinaryConjugationSection.Generation
public import Theory.Representation.BinaryConjugationSection.SL2OddFixed

/-!
# Odd centralizers in a natural binary section

A nontrivial odd subgroup survives the actor's two-group kernel. Its image
fixes no nonzero vector of the natural SL₂ module, so every fixed element
of the numerator lies in the coordinate kernel. The kernel is allowed to
have nontrivial action; its own fixed subgroup is retained exactly.

The literal application is the core quotient in DGS, *Groups and Graphs*
(1985), §9.10(1b) and (3), printed pp.147--148. This gives the radius-two
containment of its torus centralizer.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Representation.BinaryConjugationSection

variable {G : Type*} [Group G]

/-- A nontrivial odd actor fixes only representatives in the kernel of a
natural binary section. The kernel need not itself be fixed. -/
theorem natural_odd_centralizer_le_kernel
    (H A Z₀ : Subgroup G) {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
    (q : H →* SL(2,F)) (hp : IsPGroup 2 q.ker)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) SL(2,F) W)
    (c : BinaryConjugationSection H A Z₀ (σ.comp q))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (hE : ∀ g z, E (σ g z) = Matrix.mulVec g.val (E z))
    (D : Subgroup G) (hDH : D ≤ H) (ho : Odd (Nat.card D)) (hne : D ≠ ⊥) :
    A ⊓ centralizer (D : Set G) ≤ Z₀ := by
  obtain ⟨d,hd,hdne⟩ := D.bot_or_exists_ne_one.resolve_left hne
  let k : H := ⟨d,hDH hd⟩
  have hodd : Odd (orderOf k) := by
    rw [Subgroup.orderOf_mk]
    simpa only [Subgroup.orderOf_mk] using
      ho.of_dvd_nat (_root_.orderOf_dvd_natCard (⟨d,hd⟩ : D))
  have hkn : q k ≠ 1 := by
    intro hh
    have hc := hp.orderOf_coprime hodd.coprime_two_left (⟨k,hh⟩ : q.ker)
    have he : orderOf (⟨k,hh⟩ : q.ker) = orderOf k :=
      Subgroup.orderOf_mk (H := q.ker) k hh
    rw [he] at hc
    have hc' : Nat.Coprime (orderOf d) (orderOf d) := by
      simpa only [k,Subgroup.orderOf_mk] using hc
    exact hdne (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc' dvd_rfl dvd_rfl))
  apply c.centralizer_le_kernel D hDH
  intro w hw
  apply E.injective
  rw [map_zero]
  apply Matrix.SL2.odd_power_fixed_eq_zero (q k) (orderOf k) hodd
    (by rw [←map_pow,pow_orderOf_eq_one,map_one]) hkn
  rw [←hE]
  exact congrArg E (hw ⟨d,hd⟩)

/-- The fixed subgroup of the numerator is exactly the fixed subgroup of
the retained coordinate kernel. -/
theorem natural_odd_centralizer_eq_kernel_centralizer
    (H A Z₀ : Subgroup G) {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
    (q : H →* SL(2,F)) (hp : IsPGroup 2 q.ker)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) SL(2,F) W)
    (c : BinaryConjugationSection H A Z₀ (σ.comp q))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (hE : ∀ g z, E (σ g z) = Matrix.mulVec g.val (E z))
    (D : Subgroup G) (hDH : D ≤ H) (ho : Odd (Nat.card D)) (hne : D ≠ ⊥) :
    A ⊓ centralizer (D : Set G) = Z₀ ⊓ centralizer (D : Set G) :=
  le_antisymm (le_inf (natural_odd_centralizer_le_kernel H A Z₀ q hp σ c E hE D hDH ho hne)
    inf_le_right) (inf_le_inf_right _ c.kernel_le)


end Representation.BinaryConjugationSection
