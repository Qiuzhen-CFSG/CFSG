module

public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Theory.ElementaryAbelian.Quotient
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The standard binary PSL₂ torus in Proposition 16.5.1

The existing projective unipotent and diagonal homomorphisms give the actual
root group and cyclic torus. Diagonal conjugation scales the root parameter
by a square; the Frobenius map is bijective in a finite field of characteristic
two. This proves regularity, while one nonidentity diagonal element yields
all root elements as commutators. The Borel conjugation formula also proves
pointwise coverage of the full root normalizer by the torus.

These are intrinsic model calculations for the first and third paragraphs
of Aschbacher–Smith, combined manuscript (1 March 2004), Proposition 16.5.1,
printed p.1194. The containing module transports them to the prescribed
component Sylow subgroup; no ambient simplicity or group order is used.
-/

public section

open Subgroup BenderSuzuki.Converse
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.Linear
open Matrix.ProjectiveSpecialLinearGroup.OddBorel
open Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem kernel_elementary : IsElementaryAbelian 2 (kernel F) where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    rintro ⟨_, t, rfl⟩
    apply Subtype.ext
    change (unipotentHom F t) ^ 2 = 1
    rw [← map_pow]
    have ht : t ^ 2 = 1 := by
      rw [pow_two]
      change t.toAdd + t.toAdd = 0
      exact CharTwo.add_self_eq_zero _
    rw [ht, map_one]

theorem complement_cyclic : IsCyclic (complement F) :=
  (torusEquiv F).isCyclic.mp inferInstance

omit [Finite F] in
private theorem conj_torus_injective (u : F) (hu : u ≠ 0) :
    Function.Injective (fun x : complement F => MulAut.conj (x : PSL(2,F))
      (unipotentHom F (Multiplicative.ofAdd u))) := by
  intro x y h
  obtain ⟨a, ha⟩ := x.property
  obtain ⟨b, hb⟩ := y.property
  have he : (a : F)^2 * u = (b : F)^2 * u := by
    apply Multiplicative.ofAdd.injective
    apply unipotentHom_injective F
    simpa only [MulAut.conj_apply, ← ha, ← hb, torus_conj_unipotent] using h
  have hab : (a : F) = (b : F) := by
    have hsq := mul_right_cancel₀ hu he
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq).elim id (fun h => by simpa only [CharTwo.neg_eq] using h)
  apply Subtype.ext
  rw [← ha, ← hb, Units.ext hab]

theorem complement_regular {v w : PSL(2,F)} (hv : v ∈ kernel F) (hv1 : v ≠ 1)
    (hw : w ∈ kernel F) (hw1 : w ≠ 1) :
    ∃! x : complement F, MulAut.conj (x : PSL(2,F)) v = w := by
  obtain ⟨t, rfl⟩ := hv
  obtain ⟨s, rfl⟩ := hw
  have ht : t.toAdd ≠ 0 := fun h => hv1 (by rw [show t = 1 from h, map_one])
  have hs : s.toAdd ≠ 0 := fun h => hw1 (by rw [show s = 1 from h, map_one])
  obtain ⟨a, ha⟩ := isSquare_of_charTwo' (s.toAdd / t.toAdd)
  have ha0 : a ≠ 0 := by
    intro h
    simp [h, div_eq_zero_iff, hs, ht] at ha
  let x : complement F := ⟨torusHom F (Units.mk0 a ha0), ⟨_, rfl⟩⟩
  have hx : MulAut.conj (x : PSL(2,F)) (unipotentHom F t) = unipotentHom F s := by
    change torusHom F (Units.mk0 a ha0) *
      unipotentHom F (Multiplicative.ofAdd t.toAdd) * (torusHom F (Units.mk0 a ha0))⁻¹ = _
    rw [torus_conj_unipotent]
    congr 2
    change a ^ 2 * t.toAdd = s.toAdd
    rw [sq, ← ha, div_mul_cancel₀ _ ht]
  exact ⟨x, hx, fun y hy => conj_torus_injective F t.toAdd ht (hy.trans hx.symm)⟩

theorem kernel_fixed_eq_bot (hlarge : 2 < Nat.card F) :
    kernel F ⊓ centralizer (complement F : Set PSL(2,F)) = ⊥ := by
  have : Nontrivial (complement F) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [card_torus]; omega)
  obtain ⟨c, hc⟩ := exists_ne (1 : complement F)
  apply eq_bot_iff.mpr
  intro u hu
  apply mem_bot.mpr
  have he := mem_centralizer_iff.mp hu.2 c c.property
  exact congrArg Subtype.val (fixedPointFree F c hc ⟨u, hu.1⟩ (by
    change (c : PSL(2,F)) * u * (c : PSL(2,F))⁻¹ = u
    rw [he, mul_assoc, mul_inv_cancel, mul_one]))

theorem kernel_commutator (hlarge : 2 < Nat.card F) :
    ⁅kernel F, complement F⁆ = kernel F := by
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp (complement_normalizes F))
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_units]; omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  have ha2 : (a : F)^2 ≠ 1 := by
    intro h
    have he : (a : F) = 1 :=
      (sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa using h)).elim id (fun h => by simpa only [CharTwo.neg_eq] using h)
    exact ha (Units.ext he)
  rintro _ ⟨t, rfl⟩
  let b : F := t.toAdd / ((a : F)^2 - 1)
  have hc := commutator_mem_commutator (H₁ := complement F) (H₂ := kernel F)
    (show torusHom F a ∈ complement F from ⟨a, rfl⟩)
    (show unipotentHom F (Multiplicative.ofAdd b) ∈ kernel F from ⟨_, rfl⟩)
  rw [commutator_comm] at hc
  have he : ⁅torusHom F a, unipotentHom F (Multiplicative.ofAdd b)⁆ =
      unipotentHom F t := by
    rw [commutatorElement_def, torus_conj_unipotent, ← map_inv, ← map_mul]
    congr 1
    change (a : F)^2 * b + -b = t.toAdd
    dsimp [b]
    field_simp [sub_ne_zero.mpr ha2]
    ring
  rwa [he] at hc

omit [Finite F] in
theorem normalizer_coverage {g : PSL(2,F)}
    (hg : g ∈ normalizer (kernel F : Set PSL(2,F))) :
    ∃ x : complement F, ∀ u ∈ kernel F,
      MulAut.conj (x : PSL(2,F)) u = MulAut.conj g u := by
  rw [normalizer_kernel, borel_eq_PBorel, PBorel_eq_map] at hg
  obtain ⟨A, hA, rfl⟩ := hg
  let a : Fˣ := Units.mk0 (A.val 0 0) (Borel_diag_ne_zero hA)
  refine ⟨⟨torusHom F a, ⟨a, rfl⟩⟩, ?_⟩
  rintro _ ⟨t, rfl⟩
  change torusHom F a * unipotentHom F (Multiplicative.ofAdd t.toAdd) * (torusHom F a)⁻¹ = _
  rw [torus_conj_unipotent]
  change pi F (uni _) = pi F A * pi F (uni _) * (pi F A)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul, Borel_conj_uni hA]
  rfl

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.TorusConstruction.Linear
