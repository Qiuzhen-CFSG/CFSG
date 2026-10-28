module

public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage.RepresentativeCalculations.Elementary

/-!
# Extending checked J₃ basis images to binary spans

The binary multiplication law extends a homomorphism's checked basis images
to every element of a selected span. Closure under this finite action proves
normalization; induction on a positive generator word computes its action.
These helpers use the actual fixed model elements throughout.

Source: the finite-calculation route to GLS, Number 3, Table 5.3h, p.269.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations.LocalActions
open Subgroup Sporadic.Janko3 Sporadic.Janko3.TwoLocal Theory.GroupTheory
set_option Elab.async false

/-- Extend the images of the four basis elements by binary addition. -/
@[expose] public def linearImage (b : Fin 4 → Fin 16) (i : Fin 16) : Fin 16 :=
  (elementaryWord i).foldr (fun j k => xorIndex (b j) k) 0

public theorem image_elementaryElement (hS : Nat.card sylowCandidate = 128)
    (f : Model →* Model) (m : Fin 16) (b : Fin 4 → Fin 16)
    (hb : ∀ j : Fin 4, m.val.testBit j.val = true →
      f (elementaryGenerator j) = elementaryElement (b j))
    (i : Fin 16) (hi : supported m i) :
    f (elementaryElement i) = elementaryElement (linearImage b i) := by
  have hw (w : List (Fin 4)) (h : ∀ j ∈ w, m.val.testBit j.val = true) :
      f (evalWord elementaryGenerator w) =
        elementaryElement (w.foldr (fun j k => xorIndex (b j) k) 0) := by
    induction w with
    | nil => exact (map_one f).trans elementaryElement_zero.symm
    | cons j w ih =>
      simp only [evalWord, List.foldr_cons, map_mul, elementaryElement_mul hS]
      rw [hb j (h j (List.mem_cons_self ..)),
        ih (fun k hk => h k (List.mem_cons_of_mem _ hk))]
  apply hw
  have ht : ∀ m i : Fin 16, supported m i → ∀ j ∈ elementaryWord i,
      m.val.testBit j.val = true := by decide +kernel
  exact ht m i hi

public theorem normalizes_span (hS : Nat.card sylowCandidate = 128) (g : Model)
    (m : Fin 16) (b : Fin 4 → Fin 16)
    (hb : ∀ j : Fin 4, m.val.testBit j.val = true →
      (MulAut.conj g) (elementaryGenerator j) = elementaryElement (b j))
    (hs : ∀ i : Fin 16, supported m i → supported m (linearImage b i)) :
    g ∈ normalizer (elementarySpan hS m : Set Model) := by
  apply mem_normalizer_fintype
  rintro x ⟨i, hi, rfl⟩
  exact ⟨linearImage b i, hs i hi,
    (image_elementaryElement hS (MulAut.conj g).toMonoidHom m b hb i hi).symm⟩

public theorem word_image {n : Nat}
    (gen : Fin n → Model) (m : Fin 16) (act : Fin n → Fin 16 → Fin 16)
    (ha : ∀ k i, supported m i →
      (MulAut.conj (gen k)) (elementaryElement i) = elementaryElement (act k i))
    (hs : ∀ k i, supported m i → supported m (act k i))
    (w : List (Fin n)) (i : Fin 16) (hi : supported m i) :
    supported m (w.foldr act i) ∧
      (MulAut.conj (evalWord gen w)) (elementaryElement i) =
        elementaryElement (w.foldr act i) := by
  induction w with
  | nil => exact ⟨hi, by simp [evalWord]⟩
  | cons k w ih =>
    refine ⟨hs k _ ih.1, ?_⟩
    change (MulAut.conj (gen k * evalWord gen w)) (elementaryElement i) = _
    rw [map_mul]
    change (MulAut.conj (gen k)) ((MulAut.conj (evalWord gen w)) (elementaryElement i)) = _
    rw [ih.2, ha k _ ih.1]
    rfl

public theorem word_mem {n : Nat} (H : Subgroup Model) (gen : Fin n → Model)
    (hg : ∀ k, gen k ∈ H) (w : List (Fin n)) : evalWord gen w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons k w ih => exact H.mul_mem (hg k) ih

end CFSG.Quasithin.MainConverse.SporadicLocal.J3Coverage.RepresentativeCalculations.LocalActions
