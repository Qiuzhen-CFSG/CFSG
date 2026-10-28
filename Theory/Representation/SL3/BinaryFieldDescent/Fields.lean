module

public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Compatible finite fields for binary scalar descent

Finite subfields of a common field are the roots of X^q-X. This identifies
prescribed embeddings of equal-size fields, and embeds a field of order q
into one of order q^m without changing either map into the common field.
For a quadratic binary extension the smaller field is the actual fixed
subfield of the half-degree Frobenius.

These elementary finite-field facts implement the coefficient-field part of
GLS III, Remark 2.8.8, used for the SL₃ alternatives in G.9.3(8),(17).
-/

public section
open Polynomial

namespace FiniteField
variable {E F K : Type*} [Field E] [Field F] [Field K]

/-- The image of a finite field consists of exactly the roots of its cardinality polynomial. -/
theorem mem_range_iff_pow_natCard [Finite F] (ι : F →+* K) (x : K) :
    x ∈ Set.range ι ↔ x ^ Nat.card F = x := by
  let : Fintype F := Fintype.ofFinite F
  have hs : (X ^ Fintype.card F - X : F[X]).Splits := by
    rw [splits_iff_card_roots, FiniteField.roots_X_pow_card_sub_X,
      ← Finset.card_def, Finset.card_univ,
      FiniteField.X_pow_card_sub_X_natDegree_eq F Fintype.one_lt_card]
  have h := FiniteField.roots_X_pow_card_sub_X F ▸
    hs.roots_map ι ▸ Multiset.mem_map (b := x)
  simpa [sub_eq_zero, iff_comm, Nat.card_eq_fintype_card,
    FiniteField.X_pow_card_sub_X_ne_zero K Fintype.one_lt_card] using h


/-- Embed a smaller finite field into a larger one compatibly with two prescribed
embeddings into a common field. -/
theorem exists_compatible_embedding_of_card_pow [Finite E] [Finite F] (η : E →+* K) (ι : F →+* K)
    (m : ℕ) (hc : Nat.card F = Nat.card E ^ m) :
    ∃ j : E →+* F, ι.comp j = η := by
  classical
  have hh (a : E) : ∃ b : F, ι b = η a := by
    apply (mem_range_iff_pow_natCard ι (η a)).mpr
    rw [hc, ← map_pow]
    congr 1
    let : Fintype E := Fintype.ofFinite E
    simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card_pow m a
  choose j hj using hh
  refine ⟨{ toFun := j
            map_zero' := ι.injective (by rw [hj, map_zero, map_zero])
            map_one' := ι.injective (by rw [hj, map_one, map_one])
            map_add' := fun a b => ι.injective (by simp only [hj, map_add])
            map_mul' := fun a b => ι.injective (by simp only [hj, map_mul]) }, ?_⟩
  ext a
  exact hj a


/-- The half-degree Frobenius is a nonidentity involution with a fixed field
of square-root cardinality. -/
theorem binary_quadratic_frobenius_data [Finite F] [CharP F 2] (r : ℕ) (hr : 0 < r)
    (hc : Nat.card F = 2 ^ (2 * r)) :
    let σ := iterateFrobeniusEquiv F 2 r
    Function.Involutive σ ∧ σ ≠ RingEquiv.refl F ∧
      Nat.card (FixedBy.subfield F σ) = 2 ^ r := by
  let σ := iterateFrobeniusEquiv F 2 r
  have hs (a : F) : σ a = a ^ (2 ^ r) := iterateFrobeniusEquiv_def _ _ _ _
  have hf : Nat.card (FixedBy.subfield F σ) = 2 ^ r := by
    apply FiniteField.card_fixed_of_quadratic_frobenius σ 2 r hr
    · rw [hc, ← pow_mul]
      congr 1
      omega
    · exact hs
  refine ⟨?_, ?_, hf⟩
  · intro a
    rw [hs, hs, ← pow_mul, ← pow_add, ← two_mul, ← hc]
    let : Fintype F := Fintype.ofFinite F
    simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card a
  · intro he
    have hall : ∀ a : F, a ∈ FixedBy.subfield F σ := by
      intro a
      change σ a = a
      rw [show σ = RingEquiv.refl F from he]
      rfl
    have hc' : Nat.card (FixedBy.subfield F σ) = Nat.card F :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    have hlt : 2 ^ r < 2 ^ (2 * r) := Nat.pow_lt_pow_right (by decide) (by omega)
    rw [← hc, ← hc', hf] at hlt
    exact (lt_irrefl _ hlt)


/-- Equal finite cardinalities give an isomorphism compatible with the
prescribed embeddings, so arbitrary coefficient twists are retained. -/
theorem exists_compatible_equiv_of_card_eq [Finite E] [Finite F]
    (η : E →+* K) (ι : F →+* K) (hc : Nat.card F = Nat.card E) :
    ∃ e : E ≃+* F, ∀ a, ι (e a) = η a := by
  obtain ⟨j, hj⟩ := exists_compatible_embedding_of_card_pow η ι 1 (by simpa using hc)
  refine ⟨RingEquiv.ofBijective j
    ((Nat.bijective_iff_injective_and_card j).mpr ⟨j.injective, hc.symm⟩), ?_⟩
  intro a
  exact RingHom.congr_fun hj a

/-- Identify the smaller embedded binary field with the actual fixed subfield
of the half-degree Frobenius, preserving the common-field embeddings. -/
theorem exists_compatible_binary_fixedField_equiv [Finite E] [Finite F]
    (η : E →+* K) (ι : F →+* K) (σ : F ≃+* F)
    (r : ℕ) (hr : 0 < r) (hE : Nat.card E = 2 ^ r)
    (hF : Nat.card F = 2 ^ (2 * r)) (hs : ∀ a, σ a = a ^ (2 ^ r)) :
    ∃ e : E ≃+* FixedBy.subfield F σ, ∀ a, ι (e a : F) = η a := by
  have hF' : Nat.card F = (2 ^ r) ^ 2 := by
    rw [hF, ← pow_mul]
    congr 1
    omega
  have hS : Nat.card (FixedBy.subfield F σ) = 2 ^ r :=
    FiniteField.card_fixed_of_quadratic_frobenius σ 2 r hr hF' hs
  obtain ⟨j, hj⟩ := exists_compatible_embedding_of_card_pow η ι 2 (by rw [hE]; exact hF')
  let j' : E →+* FixedBy.subfield F σ :=
    { j with
      toFun a := ⟨j a, by
        change σ (j a) = j a
        rw [hs, ← hE, ← map_pow]
        congr 1
        let : Fintype E := Fintype.ofFinite E
        simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card a⟩
      map_zero' := Subtype.ext j.map_zero
      map_one' := Subtype.ext j.map_one
      map_add' a b := Subtype.ext (j.map_add a b)
      map_mul' a b := Subtype.ext (j.map_mul a b) }
  refine ⟨RingEquiv.ofBijective j'
    ((Nat.bijective_iff_injective_and_card j').mpr ⟨j'.injective, hE.trans hS.symm⟩), ?_⟩
  intro a
  exact RingHom.congr_fun hj a

end FiniteField
