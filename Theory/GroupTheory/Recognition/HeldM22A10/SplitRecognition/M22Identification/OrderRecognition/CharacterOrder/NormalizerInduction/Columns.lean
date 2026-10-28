module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysisData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.ExceptionalData
public import Theory.Character.Orthogonality
public import Theory.GroupTheory.ConjugacyClassSize

/-!
# Recovering the five special columns from scalar products

The integral inverse of the exceptional-value matrix, weighted by actual
centralizer orders, expresses each normalized class indicator as an integral
combination of the five supported functions. Pairing that identity with any
class function gives all five reciprocity formulas. Integral multiplicities
make those values real, accounting for conjugation in the scalar product.
No construction of the twelve normalizer characters is assumed proved here.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 6, p.12.
-/


open Subgroup
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy

@[expose] public def columnCoefficients : Fin 5 → Fin 5 → ℤ :=
  ![![7,-6,1,8,3], ![1,0,1,-1,0], ![-1,0,1,0,1],
    ![-1,-2,1,0,-1], ![-1,2,1,0,-1]]

@[expose] public def specialCentralizerOrders : Fin 5 → ℤ := ![384,12,8,32,16]

public theorem columnCoefficients_mul_values : ∀ r s,
    (∑ i, columnCoefficients r i * exceptionalValues i s) =
      if r = s then specialCentralizerOrders r else 0 := by decide +kernel

public theorem columnValue_eq_sum (c : Fin 5 → ℤ) (r : Fin 5) :
    columnValue c r = ∑ i, columnCoefficients r i * c i := by
  fin_cases r <;> simp [columnValue, columnCoefficients, Fin.sum_univ_succ] <;> ring

public theorem special_centralizer_orders {G : Type*} [Group G] [Finite G]
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (r : Fin 5) :
    (Nat.card (centralizer ({CaseII.into D k (specialRepresentative r)} : Set G)) : ℤ) =
      specialCentralizerOrders r := by
  fin_cases r
  · simpa [specialRepresentative, CaseII.into_z_zero, specialCentralizerOrders] using
      congrArg (Int.ofNat) D.centralizer_card
  · simpa [specialRepresentative, specialCentralizerOrders] using
      congrArg (Int.ofNat) (L.centralizer_orders 3)
  · simpa [specialRepresentative, specialCentralizerOrders] using
      congrArg (Int.ofNat) (L.centralizer_orders 2)
  · simpa [specialRepresentative, specialCentralizerOrders] using
      congrArg (Int.ofNat) (L.centralizer_orders 0)
  · simpa [specialRepresentative, specialCentralizerOrders] using
      congrArg (Int.ofNat) (L.centralizer_orders 1)

private theorem class_eq_of_conj {H : Type*} [Group H] {f : ClassFunction H}
    (hf : IsClassFunction f) {a b : H} (h : IsConj a b) : f a = f b := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact (hf a g).symm

private theorem scalar_sum {H I : Type*} [Fintype H] [Fintype I]
    (f : I → ClassFunction H) (g : ClassFunction H) :
    scalarProduct H (∑ i, f i) g = ∑ i, scalarProduct H (f i) g := by
  simp only [scalarProduct, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]

public theorem columns_of_supported_values {G : Type*} [Group G] [Finite G]
    (D : LocalData G) (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)
    (ψ : Fin 5 → ClassFunction G) (hc : ∀ i, IsClassFunction (ψ i))
    (hv : ∀ i r, ψ i (CaseII.into D k (specialRepresentative r)) = (exceptionalValues i r : ℂ))
    (hs : ∀ i g, (∀ r, ¬ IsConj g (CaseII.into D k (specialRepresentative r))) → ψ i g = 0)
    (χ : ClassFunction G) (hχ : IsClassFunction χ) (c : Fin 5 → ℤ)
    (hm : ∀ i, scalarProduct G (ψ i) χ = (c i : ℂ)) (r : Fin 5) :
    χ (CaseII.into D k (specialRepresentative r)) = (columnValue c r : ℂ) := by
  classical
  let t : Fin 5 → G := fun s => CaseII.into D k (specialRepresentative s)
  have hsep {a b : Fin 5} (h : IsConj (t a) (t b)) : a = b := by
    have he : ∀ i, exceptionalValues i a = exceptionalValues i b := by
      intro i
      have h' := class_eq_of_conj (hc i) h
      rw [hv, hv] at h'
      exact_mod_cast h'
    have hnum : ∀ a b : Fin 5, (∀ i, exceptionalValues i a = exceptionalValues i b) → a = b := by
      decide +kernel
    exact hnum a b he
  have hcard : (Nat.card G : ℂ) / (Nat.card (ConjClasses.mk (t r)).carrier : ℂ) =
      (specialCentralizerOrders r : ℂ) := by
    have h : Nat.card (ConjClasses.mk (t r)).carrier *
        Nat.card (centralizer ({t r} : Set G)) = Nat.card G := by
      rw [ConjClasses.nat_card_carrier_eq_index_centralizer, Subgroup.index_mul_card]
    have hn : Nat.card (ConjClasses.mk (t r)).carrier ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at h
      exact (Nat.card_pos (α := G)).ne' h.symm
    have hn' : (Nat.card (ConjClasses.mk (t r)).carrier : ℂ) ≠ 0 := by exact_mod_cast hn
    apply (div_eq_iff hn').mpr
    have hC := special_centralizer_orders D k L r
    have hC' : (Nat.card (centralizer ({t r} : Set G)) : ℂ) =
        (specialCentralizerOrders r : ℂ) := by exact_mod_cast hC
    rw [← hC']
    exact_mod_cast h.symm.trans (Nat.mul_comm _ _)
  have he : (∑ i, (columnCoefficients r i : ℂ) • ψ i) =
      ofConjClassFunction (classProjection (ConjClasses.mk (t r))) := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ofConjClassFunction]
    by_cases hg : ∃ s, IsConj g (t s)
    · obtain ⟨s, hs'⟩ := hg
      have hg' := ConjClasses.mk_eq_mk_iff_isConj.mpr hs'
      simp only [hg']
      have he' : ∀ i, ψ i g = (exceptionalValues i s : ℂ) := by
        intro i
        exact (class_eq_of_conj (hc i) hs').trans (hv i s)
      simp only [he', ← Int.cast_mul, ← Int.cast_sum, columnCoefficients_mul_values]
      by_cases hrs : r = s
      · subst s
        rw [if_pos rfl, classProjection_apply_eq, hcard]
      · rw [if_neg hrs, Int.cast_zero, classProjection_apply_ne]
        intro h
        exact hrs (hsep (ConjClasses.mk_eq_mk_iff_isConj.mp h)).symm
    · have hz : ∀ i, ψ i g = 0 := fun i => hs i g (not_exists.mp hg)
      simp only [hz, mul_zero, Finset.sum_const_zero]
      symm
      apply classProjection_apply_ne
      intro h
      exact hg ⟨r, ConjClasses.mk_eq_mk_iff_isConj.mp h⟩
  have hi := congrArg (fun f => scalarProduct G f χ) he
  rw [scalar_sum] at hi
  simp only [scalarProduct_smul_left, hm, ← Int.cast_mul, ← Int.cast_sum,
    ← columnValue_eq_sum] at hi
  have hi' : scalarProduct G (ofConjClassFunction (classProjection (ConjClasses.mk (t r)))) χ =
      star (χ (t r)) := by
    exact classProjection_inner (ConjClasses.mk (t r)) (toConjClassFunction χ hχ)
  rw [hi'] at hi
  have hj := congrArg star hi.symm
  simpa using hj
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
