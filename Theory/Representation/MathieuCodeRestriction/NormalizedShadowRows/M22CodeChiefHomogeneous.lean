module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeChiefNatural
public import Theory.Representation.HomogeneousNormalizerSeed
public import Theory.Representation.TensorInvolutionDisplacement

/-!
# Homogeneous natural coordinates from the M22 chief displacement

The original residual image is normal. Commuting generators preserve its
natural type, while the supplement preserves the actual displacement seed.
Clifford theory consequently supplies homogeneous coordinates on the entire
irreducible module. The involution displacement has binary dimension four,
so at least two natural copies occur. The coordinates retain the original
A5 marking and its whole two-core quotient.

Source: Aschbacher--Smith 8.2.9, printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement MonoidAlgebra MatrixGroups
namespace MathieuCode.NormalizedShadowRows.M22CodeSection
set_option backward.isDefEq.respectTransparency false

/-- Normality of the original residual image and the actual seed stabilizer
force homogeneous natural coordinates for the whole irreducible module. -/
theorem M22NaturalChiefDisplacement.homogeneous_coordinates
    {A R Z : Type*} [Group A] [Group R] [AddCommGroup Z] [Module (ZMod 2) Z]
    [FiniteDimensional (ZMod 2) Z]
    (ρ : Representation (ZMod 2) A Z) [IsIrreducible ρ]
    (a : R →* A) [a.range.Normal] (r : R →* alternatingGroup (Fin 5))
    (y : A) (h : M22NaturalChiefDisplacement ρ a r y)
    (C P : Subgroup A) (hgen : (a.range ⊔ C) ⊔ P = ⊤)
    (hC : ∀ c ∈ C, ∀ x : R, Commute (ρ c) (ρ (a x)))
    (hP : ∀ p ∈ P, (LinearMap.range (ρ y - 1)).map (ρ p) = LinearMap.range (ρ y - 1)) :
    ∃ m : ℕ, ∃ e : Z ≃ₗ[ZMod 2] (Fin m → (Fin 2 → GaloisField 2 2)),
      (∀ x z, e (ρ (a x) z) =
        fun i => specialLinearNatural 2 (fiveMovedSL2Marking (r x)) (e z i)) ∧
      Module.finrank (ZMod 2) Z = m * 4 := by
  obtain ⟨S,hSi,hS,hd,eN,heN⟩ := h
  let S₀ : Subrepresentation (ρ.comp a.range.subtype) := {
    toSubmodule := S.toSubmodule
    apply_mem_toSubmodule x z hz := by
      change ρ (x : A) z ∈ S.toSubmodule
      obtain ⟨x,hx⟩ := x.property
      rw [←hx]
      exact S.apply_mem_toSubmodule x hz }
  have hSi₀ : IsIrreducible S₀.toRepresentation :=
    (irreducible_comp_surjective_iff a.rangeRestrict a.rangeRestrict_surjective
      S₀.toRepresentation).mp hSi
  have hC₀ : ∀ c ∈ C, ∀ x : a.range, Commute (ρ c) (ρ x) := by
    intro c hc x
    obtain ⟨x,hx⟩ := x.property
    rw [←hx]
    exact hC c hc x
  have hP₀ : ∀ p ∈ P, S₀.toSubmodule.map (ρ p) = S₀.toSubmodule := by
    intro p hp
    change S.toSubmodule.map (ρ p) = S.toSubmodule
    rw [hS]
    exact hP p hp
  obtain ⟨m,b,hb⟩ := Representation.homogeneous_coordinates_of_commuting_and_stable
    ρ a.range C P hgen S₀ hSi₀ hC₀ hP₀
  let e : Z ≃ₗ[ZMod 2] (Fin m → (Fin 2 → GaloisField 2 2)) :=
    b.trans (LinearEquiv.piCongrRight fun _ => eN)
  refine ⟨m,e,?_,?_⟩
  · intro x z
    have hh := hb (a.rangeRestrict x) z
    change b (ρ (a x) z) = _ at hh
    funext i
    change eN (b (ρ (a x) z) i) = _
    rw [hh]
    exact heN x (b z i)
  · have hdS : Module.finrank (ZMod 2) S.toSubmodule = 4 := hS ▸ hd
    rw [b.finrank_eq,Module.finrank_pi_fintype]
    change (∑ _ : Fin m, Module.finrank (ZMod 2) S.toSubmodule) = m*4
    simp only [hdS,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]

/-- Homogeneous natural coordinates retain the entire original residual
quotient and its given A5 marking. -/
@[expose] def M22NaturalHomogeneousCoordinates
    {A R Z : Type*} [Group A] [Group R] [AddCommGroup Z] [Module (ZMod 2) Z]
    (ρ : Representation (ZMod 2) A Z) (a : R →* A)
    (r : R →* alternatingGroup (Fin 5)) : Prop :=
  ∃ m : ℕ, 2 ≤ m ∧ ∃ eR : (R ⧸ pCore 2 R) ≃* SL(2,GaloisField 2 2),
    ∃ e : Z ≃ₗ[ZMod 2] (Fin m → (Fin 2 → GaloisField 2 2)),
      (∀ x, eR (QuotientGroup.mk' (pCore 2 R) x) = fiveMovedSL2Marking (r x)) ∧
      (∀ x z, e (ρ (a x) z) =
        fun i => specialLinearNatural 2 (eR (QuotientGroup.mk' (pCore 2 R) x)) (e z i)) ∧
      Module.finrank (ZMod 2) Z = m * 4

theorem natural_homogeneous_coordinates_of_marking
    {A R Z : Type*} [Group A] [Group R] [AddCommGroup Z] [Module (ZMod 2) Z]
    [FiniteDimensional (ZMod 2) Z]
    (ρ : Representation (ZMod 2) A Z) (a : R →* A)
    (r : R →* alternatingGroup (Fin 5))
    (hrs : Function.Surjective r) (hrker : r.ker = pCore 2 R)
    (y : A) (hy : y^2=1)
    (hy4 : Module.finrank (ZMod 2) (LinearMap.range (ρ y-1))=4)
    (m : ℕ) (e : Z ≃ₗ[ZMod 2] (Fin m → (Fin 2 → GaloisField 2 2)))
    (he : ∀ x z, e (ρ (a x) z) =
      fun i => specialLinearNatural 2 (fiveMovedSL2Marking (r x)) (e z i))
    (hd : Module.finrank (ZMod 2) Z = m * 4) :
    M22NaturalHomogeneousCoordinates ρ a r := by
  have hdim := TensorInvolutionDisplacement.twice_displacement_le (ρ y)
    (by rw [←map_mul,←pow_two,hy,map_one])
  change 2 * Module.finrank (ZMod 2) (LinearMap.range (ρ y-1)) ≤ _ at hdim
  rw [hy4,hd] at hdim
  have hm : 2 ≤ m := by omega
  let eR : (R ⧸ pCore 2 R) ≃* SL(2,GaloisField 2 2) :=
    ((QuotientGroup.quotientMulEquivOfEq hrker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective r hrs)).trans fiveMovedSL2Marking
  exact ⟨m,hm,eR,e,fun _ => rfl,he,hd⟩

end MathieuCode.NormalizedShadowRows.M22CodeSection
