module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.Transport
public import Theory.Representation.BinaryOffender.DualDisplacement

/-!
# Defining-field displacement bounds for the SL₃ extension argument

The binary commutator span of an F-linear action is already F-stable.
Consequently its binary dimension is the field degree times its F-dimension.
Displacement embeds the actor in Hom_F(V/C_V(A), [V,A]). In dimension three,
quadraticity puts the commutator in the fixed space, so the two positive
F-dimensions have sum at most three. Their product is at most two and is
strictly smaller than their sum.

These estimates give the actor-rank bound and exclude the natural-by-dual
FF extension in the literal DoubleNatural application in the parent module.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.9(2),
printed p.94, together with the displacement argument in K.3.2.1.
-/

public section
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterK.Linear.Natural

namespace CFSG.Quasithin.ChapterB.NaturalExtensions.LargerFieldThree
variable (F : BinaryField) (n : ℕ)

noncomputable abbrev fieldCommutator
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin n) F.Carrier)) :=
  Coinvariants.ker ((specialLinearNatural (k := F.Carrier) n).comp A.subtype)

theorem fieldCommutator_restrictScalars
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin n) F.Carrier)) :
    (fieldCommutator F n A).restrictScalars (ZMod 2) =
      Coinvariants.ker ((linearNatural F n).comp A.subtype) := by
  let C := Coinvariants.ker ((linearNatural F n).comp A.subtype)
  have hsmul (c : F.Carrier) {v : Fin n → F.Carrier} (hv : v ∈ C) : c • v ∈ C := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨g, w⟩, rfl⟩ := hv
      have h := Coinvariants.sub_mem_ker (ρ := (linearNatural F n).comp A.subtype)
        g (c • w)
      change specialLinearNatural n g.val (c • w) - c • w ∈ C at h
      change c • (specialLinearNatural (k := F.Carrier) n g.val w - w) ∈ C
      simpa only [map_smul, smul_sub] using h
    | zero => simp only [smul_zero]; exact C.zero_mem
    | add x y hx hy ihx ihy => simpa only [smul_add] using C.add_mem ihx ihy
    | smul b x hx ih => simpa only [smul_comm c b x] using C.smul_mem b ih
  let D : Submodule F.Carrier (Fin n → F.Carrier) :=
    { C.toAddSubmonoid with smul_mem' := fun c v hv => hsmul c hv }
  apply le_antisymm
  · have h : fieldCommutator F n A ≤ D := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g, w⟩, rfl⟩
      exact Coinvariants.sub_mem_ker (ρ := (linearNatural F n).comp A.subtype) g w
    exact h
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, w⟩, rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := (specialLinearNatural n).comp A.subtype) g w

theorem dual_fixedCodim_eq_field_commutator
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin n) F.Carrier)) :
    fixedCodim (linearNatural F n).dual A =
      F.degree * Module.finrank F.Carrier (fieldCommutator F n A) := by
  have h := finrank_dual_quotient_invariants ((linearNatural F n).comp A.subtype)
  change fixedCodim (linearNatural F n).dual A =
    Module.finrank (ZMod 2) (Coinvariants.ker ((linearNatural F n).comp A.subtype)) at h
  rw [h, ← fieldCommutator_restrictScalars]
  change Module.finrank (ZMod 2) (fieldCommutator F n A) = _
  rw [← Module.finrank_mul_finrank (ZMod 2) F.Carrier, field_finrank]

theorem field_displacement_rank_bound
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin n) F.Carrier)) :
    rank A ≤ F.degree *
      (Module.finrank F.Carrier ((Fin n → F.Carrier) ⧸ fieldFixedSpace F n A) *
        Module.finrank F.Carrier (fieldCommutator F n A)) := by
  classical
  let C := fieldFixedSpace F n A
  let D := fieldCommutator F n A
  let σ := specialLinearNatural (k := F.Carrier) n
  let d (a : A) : (Fin n → F.Carrier) →ₗ[F.Carrier] D :=
    (σ a - LinearMap.id).codRestrict D (fun v =>
      Coinvariants.sub_mem_ker (ρ := σ.comp A.subtype) a v)
  let f (a : A) : ((Fin n → F.Carrier) ⧸ C) →ₗ[F.Carrier] D :=
    C.liftQ (d a) (by
      intro v hv
      apply Subtype.ext
      exact sub_eq_zero.mpr (hv a))
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply specialLinearNatural_injective n
    apply LinearMap.ext
    intro v
    have hv := congrArg (fun l : ((Fin n → F.Carrier) ⧸ C) →ₗ[F.Carrier] D =>
      (l (C.mkQ v) : Fin n → F.Carrier)) he
    change σ a v - v = σ b v - v at hv
    exact sub_left_injective hv
  let : Finite (((Fin n → F.Carrier) ⧸ C) →ₗ[F.Carrier] D) :=
    Module.finite_of_finite F.Carrier
  have hc := Nat.card_le_card_of_injective f hf
  rw [Module.natCard_eq_pow_finrank (K := F.Carrier)
      (V := ((Fin n → F.Carrier) ⧸ C) →ₗ[F.Carrier] D),
    Module.finrank_linearMap, F.card_eq, ← pow_mul] at hc
  have hl := Nat.log_monotone (b := 2) hc
  rw [Nat.log_pow (by decide : 1 < 2)] at hl
  exact hl

theorem quadratic_field_dimensions
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin n) F.Carrier)}
    (hq : IsQuadratic (linearNatural F n) A) :
    Module.finrank F.Carrier ((Fin n → F.Carrier) ⧸ fieldFixedSpace F n A) +
      Module.finrank F.Carrier (fieldCommutator F n A) ≤ n := by
  have hle : fieldCommutator F n A ≤ fieldFixedSpace F n A := by
    apply (commutator_le_invariants_iff _).mpr
    intro a b v
    exact hq a a.property b b.property v
  have hl := Submodule.finrank_mono hle
  have hd := (fieldFixedSpace F n A).finrank_quotient_add_finrank
  simp only [Module.finrank_pi, Fintype.card_fin] at hd
  omega

theorem field_dimensions_pos
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin n) F.Carrier)} (hne : A ≠ ⊥) :
    0 < Module.finrank F.Carrier ((Fin n → F.Carrier) ⧸ fieldFixedSpace F n A) ∧
      0 < Module.finrank F.Carrier (fieldCommutator F n A) := by
  have h₁ := fixedCodim_pos_of_faithful (linearNatural F n) (natural_injective F n) hne
  have h₂ := fixedCodim_pos_of_faithful (linearNatural F n).dual
    (faithful_dual _ (natural_injective F n)) hne
  rw [fixedCodim_eq_field_codim] at h₁
  rw [dual_fixedCodim_eq_field_commutator] at h₂
  exact ⟨(Nat.pos_of_mul_pos_left h₁), (Nat.pos_of_mul_pos_left h₂)⟩

private theorem product_bound {c r : ℕ} (hc : 0 < c) (hr : 0 < r) (h : c + r ≤ 3) :
    c * r ≤ 2 ∧ c * r < c + r := by
  have hh : c = 1 ∨ r = 1 := by omega
  rcases hh with rfl | rfl <;> simp only [one_mul, mul_one] <;> omega

theorem quadratic_three_rank_bound
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F.Carrier)}
    (hne : A ≠ ⊥) (hq : IsQuadratic (linearNatural F 3) A) : rank A ≤ 2 * F.degree := by
  obtain ⟨hc, hr⟩ := field_dimensions_pos F 3 hne
  have hp := (product_bound hc hr (quadratic_field_dimensions F 3 hq)).1
  exact (field_displacement_rank_bound F 3 A).trans
    (by simpa only [mul_comm 2] using Nat.mul_le_mul_left F.degree hp)

theorem quadratic_three_dual_cost
    {A : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F.Carrier)}
    (hne : A ≠ ⊥) (hq : IsQuadratic (linearNatural F 3) A) :
    rank A < fixedCodim (linearNatural F 3) A + fixedCodim (linearNatural F 3).dual A := by
  obtain ⟨hc, hr⟩ := field_dimensions_pos F 3 hne
  have hp := (product_bound hc hr (quadratic_field_dimensions F 3 hq)).2
  rw [fixedCodim_eq_field_codim, dual_fixedCodim_eq_field_commutator, ← mul_add]
  exact (field_displacement_rank_bound F 3 A).trans_lt
    (Nat.mul_lt_mul_of_pos_left hp F.degree_pos)

end CFSG.Quasithin.ChapterB.NaturalExtensions.LargerFieldThree
