module
public import Theory.SpecificGroups.SL2.PRegularTraceConjugacy
public import Theory.Representation.PRegularTrace

/-!
# The number of p-regular SL2 conjugacy classes

Over a finite field K of characteristic p, the actual conjugacy classes
represented by elements of SL2(K) whose order is prime to p are in bijection
with K via trace. This includes characteristic two and the field of order
three, and gives the class count needed to exhaust the simple SL2 modules.

The trace-conjugacy theorem proves injectivity with an actual determinant-one
conjugator. For surjectivity, the companion matrix [[0,-1],[1,t]] has trace t;
the simultaneous p-regular character-reduction theorem replaces it by a
p-regular element with the same trace in the standard representation. Choosing
representatives of the actual ConjClasses image then gives a bijection. No
alternative class relation or formal character-parameter set is introduced.
-/

namespace Matrix.SpecialLinearGroup
variable {K : Type*} [Field K] [Finite K] {p : ℕ} [CharP K p]

private theorem card_of_trace_surjective
    (hsurj : ∀ t : K, ∃ g : SpecialLinearGroup (Fin 2) K,
      ¬ p ∣ orderOf g ∧ Matrix.trace (g : Matrix (Fin 2) (Fin 2) K) = t) :
    Nat.card (ConjClasses.mk '' {g : SpecialLinearGroup (Fin 2) K | ¬ p ∣ orderOf g}) =
      Nat.card K := by
  classical
  let P := ConjClasses.mk '' {g : SpecialLinearGroup (Fin 2) K | ¬ p ∣ orderOf g}
  have hrep (c : P) : ∃ g : SpecialLinearGroup (Fin 2) K,
      ¬ p ∣ orderOf g ∧ ConjClasses.mk g = c.1 := c.2
  let r : P → SpecialLinearGroup (Fin 2) K := fun c => (hrep c).choose
  have hrp (c : P) : ¬ p ∣ orderOf (r c) := (hrep c).choose_spec.1
  have hrc (c : P) : ConjClasses.mk (r c) = c.1 := (hrep c).choose_spec.2
  let tr : P → K := fun c => Matrix.trace (r c : Matrix (Fin 2) (Fin 2) K)
  have hinj : Function.Injective tr := by
    intro c d h
    apply Subtype.ext
    rw [← hrc c, ← hrc d]
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    exact (isConj_iff_trace_eq_of_pRegular (r c) (r d) (hrp c) (hrp d)).mpr h
  have hsur : Function.Surjective tr := by
    intro t
    obtain ⟨g, hgp, hgt⟩ := hsurj t
    let c : P := ⟨ConjClasses.mk g, g, hgp, rfl⟩
    refine ⟨c, ?_⟩
    have hc : IsConj (r c) g := ConjClasses.mk_eq_mk_iff_isConj.mp (hrc c)
    exact ((isConj_iff_trace_eq_of_pRegular (r c) g (hrp c) hgp).mp hc).trans hgt
  exact Nat.card_congr (Equiv.ofBijective tr ⟨hinj, hsur⟩)

private noncomputable def standardRepresentation :
    Representation K (SpecialLinearGroup (Fin 2) K) (Fin 2 → K) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp SpecialLinearGroup.toLin'

omit [Finite K] in
private theorem standardRepresentation_character (g : SpecialLinearGroup (Fin 2) K) :
    (standardRepresentation (K := K)).character g = Matrix.trace (g : Matrix (Fin 2) (Fin 2) K) := by
  change LinearMap.trace K (Fin 2 → K) (Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) K)) = _
  exact Matrix.trace_toLin'_eq _

public theorem card_pRegularConjClasses (K : Type*) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    Nat.card (ConjClasses.mk '' {g : SpecialLinearGroup (Fin 2) K | ¬ p ∣ orderOf g}) =
      Nat.card K := by
  apply card_of_trace_surjective
  intro t
  let A : SpecialLinearGroup (Fin 2) K := ⟨!![0, -1; 1, t], by simp⟩
  obtain ⟨h, hhp, hchar⟩ := Representation.exists_pRegular_same_character (F := K) p A
  have hht := (hchar (Fin 2 → K) (standardRepresentation (K := K))).symm
  refine ⟨h, hhp, ?_⟩
  rw [standardRepresentation_character, standardRepresentation_character] at hht
  simpa [A, Matrix.trace_fin_two] using hht

end Matrix.SpecialLinearGroup
