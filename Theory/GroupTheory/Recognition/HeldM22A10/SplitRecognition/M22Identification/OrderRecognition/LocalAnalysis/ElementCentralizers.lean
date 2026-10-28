module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData

/-!
# Centralizers of the four noninvolutory Case II representatives

Each representative has a power equal to the marked involution. Thus an
ambient element centralizing it is in the known involution centralizer.
The resulting centralizer orders are finite calculations in the local model.
In particular, the two representatives of order four cannot be conjugate.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1–19, Section 5, pp.8–10.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy
namespace CaseII
universe u

local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm
local instance (v : TwistedModel) : DecidablePred (· ∈ centralizer ({v} : Set TwistedModel)) :=
  fun x => decidable_of_iff (x * v = v * x) mem_centralizer_singleton_iff.symm

/-- The squares, fourth power, and cube reduce centralizer computations to `C(z)`. -/
public theorem representative_powers : ∀ i : Fin 4,
    (![z 3 * a, z 1 * d, z 1 * b * d, c * z 0] i) ^ (![2, 2, 4, 3] i) = z 0 := by
  decide +kernel

/-- The four centralizer orders, computed inside the actual coordinate model. -/
public theorem model_centralizer_orders : ∀ i : Fin 4,
    Nat.card (centralizer ({![z 3 * a, z 1 * d, z 1 * b * d, c * z 0] i} :
      Set TwistedModel)) = ![32, 16, 8, 12] i := by
  intro i
  rw [Nat.card_eq_fintype_card]
  have h : ∀ i : Fin 4,
      Fintype.card (centralizer ({![z 3 * a, z 1 * d, z 1 * b * d, c * z 0] i} :
        Set TwistedModel)) = ![32, 16, 8, 12] i := by decide +kernel
  exact h i

variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- Centralizers of roots of the distinguished involution transport without
loss from the model to the ambient group. -/
public theorem centralizer_root_map (v : TwistedModel) (n : ℕ) (hv : v ^ n = z 0) :
    centralizer ({into D k v} : Set G) =
      (centralizer ({v} : Set TwistedModel)).map (into D k) := by
  apply le_antisymm
  · intro x hx
    have hc : Commute x (into D k v) := mem_centralizer_singleton_iff.mp hx
    have hxC : x ∈ D.centralizer := by
      apply mem_centralizer_singleton_iff.mpr
      simpa only [← map_pow, hv, into_z_zero D k] using (hc.pow_right n).eq
    obtain ⟨y, hy⟩ := k.surjective ⟨x, hxC⟩
    have hyx : into D k y = x := congrArg Subtype.val hy
    refine ⟨y, mem_centralizer_singleton_iff.mpr ?_, hyx⟩
    apply into_injective D k
    simpa only [map_mul, hyx] using hc.eq
  · rintro x ⟨y, hy, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg (into D k) (mem_centralizer_singleton_iff.mp hy)

/-- Lemma 10's four centralizer orders hold in the ambient group. -/
public theorem centralizer_orders : ∀ i : Fin 4,
    Nat.card (centralizer ({into D k
      (![z 3 * a, z 1 * d, z 1 * b * d, c * z 0] i)} : Set G)) =
      ![32, 16, 8, 12] i := by
  intro i
  rw [centralizer_root_map D k _ _ (representative_powers i),
    ← Nat.card_congr ((centralizer ({![z 3 * a, z 1 * d, z 1 * b * d, c * z 0] i} :
      Set TwistedModel)).equivMapOfInjective (into D k) (into_injective D k)).toEquiv]
  exact model_centralizer_orders i

private theorem centralizer_card_conj {A : Type*} [Group A] {x y : A}
    (h : IsConj x y) : Nat.card (centralizer ({x} : Set A)) =
      Nat.card (centralizer ({y} : Set A)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  let e := MulAut.conj g
  have he : e x = y := hg
  apply Nat.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)
  intro t
  change t ∈ centralizer ({x} : Set A) ↔ e t ∈ centralizer ({y} : Set A)
  simp only [mem_centralizer_singleton_iff, ← he, ← map_mul, e.injective.eq_iff]

/-- The two source representatives of order four are not conjugate in `G`. -/
public theorem four_not_fused : ¬ IsConj (into D k (z 3 * a)) (into D k (z 1 * d)) := by
  intro h
  have hc := centralizer_card_conj h
  have h0 := centralizer_orders D k 0
  have h1 := centralizer_orders D k 1
  change Nat.card (centralizer ({into D k (z 3 * a)} : Set G)) = 32 at h0
  change Nat.card (centralizer ({into D k (z 1 * d)} : Set G)) = 16 at h1
  omega

end CaseII
end Theory.GroupTheory.HeldM22A10.M22Identification
