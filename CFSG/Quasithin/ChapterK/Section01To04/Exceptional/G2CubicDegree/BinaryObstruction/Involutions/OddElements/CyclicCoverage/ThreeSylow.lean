module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.CyclicCoverage.Certificates

/-!
# Regular-three fusion inside the actual derived binary G₂ group

The certified 27 words form a subgroup of order 27. Since its index is 224,
it is a Sylow three-subgroup. Every three-element is conjugate into it.
The three central rows have centralizers containing this entire subgroup;
therefore centralizer order nine excludes precisely those rows. All remaining
rows are explicitly conjugate to the same marked word `a*b`.

Thus the proof retains the distinction between the two order-three classes.
The downstream application is the regular-three clause of cyclic coverage
for Guralnick–Malle, Classification of 2F-modules I, Proposition 4.3, pp.10–11.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.CyclicCoverageCertificate
open Subgroup
open G2DerivedPermutationFiltration.VertexCoordinates

def sylowElement (i : Fin 27) : Actor := eval (sylowWords i)

theorem sylowElement_action (i : Fin 27) (k : Fin 63) :
    action (sylowElement i) k = sylowTable i k := by
  rw [sylowElement, action_eval]
  exact words_correct i k

theorem sylowElement_mul (i j : Fin 27) :
    sylowElement i * sylowElement j = sylowElement (mulTable i j) := by
  apply action_injective
  apply Equiv.ext
  intro k
  simp only [map_mul, Equiv.Perm.mul_apply, sylowElement_action]
  exact multiplication_correct i j k

theorem sylowElement_zero : sylowElement 0 = 1 := rfl

theorem sylowElement_inv (i : Fin 27) :
    sylowElement (invTable i) = (sylowElement i)⁻¹ := by
  apply mul_left_cancel (a := sylowElement i)
  rw [sylowElement_mul, inverse_correct, sylowElement_zero, mul_inv_cancel]

theorem sylowElement_injective : Function.Injective sylowElement := by
  intro i j hij
  apply separation_correct
  have h := congrArg (fun g : Actor => action g 0) hij
  simpa only [sylowElement_action] using h

def threeSubgroup : Subgroup Actor where
  carrier := Set.range sylowElement
  one_mem' := ⟨0, sylowElement_zero⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨mulTable i j, (sylowElement_mul i j).symm⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨invTable i, sylowElement_inv i⟩

theorem card_threeSubgroup : Nat.card threeSubgroup = 27 := by
  let e : Fin 27 ≃ threeSubgroup := Equiv.ofBijective (fun i => ⟨sylowElement i, ⟨i, rfl⟩⟩)
    ⟨fun i j h => sylowElement_injective (congrArg Subtype.val h), by
      rintro ⟨x, i, rfl⟩
      exact ⟨i, rfl⟩⟩
  exact (Nat.card_congr e.symm).trans (Nat.card_fin 27)

private instance three_prime : Fact (Nat.Prime 3) := ⟨by decide⟩

def threeSylow : Sylow 3 Actor :=
  (IsPGroup.of_card (n := 3) card_threeSubgroup).toSylow (by
    have h := threeSubgroup.card_mul_index
    rw [card_threeSubgroup, card_actor] at h
    have hi : threeSubgroup.index = 224 := by omega
    rw [hi]
    decide)

theorem central_rows (i : Fin 27) (hi : i = 0 ∨ i = 25 ∨ i = 26) :
    threeSubgroup ≤ centralizer ({sylowElement i} : Set Actor) := by
  rintro _ ⟨j, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  rw [sylowElement_mul, sylowElement_mul, central_correct i hi j]

theorem noncentral_fusion (i : Fin 27) (hi : ¬ (i = 0 ∨ i = 25 ∨ i = 26)) :
    IsConj (groupGenerator 0 * groupGenerator 1) (sylowElement i) := by
  apply isConj_iff.mpr
  refine ⟨eval (fusionWords i), ?_⟩
  apply mul_right_cancel (b := eval (fusionWords i))
  rw [inv_mul_cancel_right]
  apply action_injective
  apply Equiv.ext
  intro k
  simp only [map_mul, action_generator, action_eval, Equiv.Perm.mul_apply,
    sylowElement_action, fusion_words_correct]
  exact fusion_correct i hi k

private theorem centralizer_card_conjugate {x y : Actor} (h : IsConj x y) :
    Nat.card (centralizer ({x} : Set Actor)) = Nat.card (centralizer ({y} : Set Actor)) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  let f := MulAut.conj g
  apply Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)
  intro a
  change a ∈ centralizer ({x} : Set Actor) ↔ f a ∈ centralizer ({f x} : Set Actor)
  simp only [mem_centralizer_singleton_iff, ← map_mul, f.injective.eq_iff]

/-- Only the regular cubic class survives the centralizer-order-nine hypothesis. -/
theorem regular_three_fusion (x : Actor) (hx : orderOf x = 3)
    (hc : Nat.card (centralizer ({x} : Set Actor)) = 9) :
    IsConj (groupGenerator 0 * groupGenerator 1) x := by
  obtain ⟨y, hy⟩ := threeSylow.exists_isConj_of_orderOf_eq_prime_pow
    (hx.trans (pow_one 3).symm)
  obtain ⟨i, hi⟩ := y.property
  have hconj : IsConj x (sylowElement i) := hi.symm ▸ hy
  have hnot : ¬ (i = 0 ∨ i = 25 ∨ i = 26) := by
    intro hz
    have hdiv := card_dvd_of_le (central_rows i hz)
    rw [card_threeSubgroup, ← centralizer_card_conjugate hconj, hc] at hdiv
    norm_num at hdiv
  exact (noncentral_fusion i hnot).trans hconj.symm

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.Involutions.OddElements.CyclicCoverageCertificate
