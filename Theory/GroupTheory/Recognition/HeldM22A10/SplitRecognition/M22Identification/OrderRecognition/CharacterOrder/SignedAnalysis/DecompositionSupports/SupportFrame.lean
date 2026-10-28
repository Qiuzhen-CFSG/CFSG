module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.IntegralExpansion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.SignedAnalysis.SignedCoordinates

/-!
# Enumerating signed supports in the complete character basis

A frame records distinct signed nonprincipal indices in an actual integral
character expansion. Splitting the squared norm leaves a finite set of unused
coordinates. Unit multiplicities make its squared norm equal its support size;
enumerating that support extends the frame and gives the full class-function
identity. No assertion that a list of support patterns is exhaustive is assumed.

Source: the support argument in Janko, *A characterization of the Mathieu simple
groups, I*, J. Algebra 9 (1968), Lemma 12, p.13.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G]
namespace SignedAnalysis.DecompositionSupports

private theorem enumerate_support {J : Type*} [Fintype J] (s : Finset J)
    (a : J → ℤ) (ha : ∀ j, a j = 0 ∨ a j = 1 ∨ a j = -1)
    (n : ℕ) (hn : ∑ j ∈ s, a j ^ 2 = (n : ℤ)) :
    ∃ p : Fin n → J, Function.Injective p ∧
      (∀ r, p r ∈ s ∧ (a (p r) = 1 ∨ a (p r) = -1)) ∧
      ∀ {M : Type u} [AddCommMonoid M] (f : J → M),
        (∀ j, a j = 0 → f j = 0) → ∑ j ∈ s, f j = ∑ r, f (p r) := by
  classical
  let t := s.filter (fun j => a j ≠ 0)
  have ht (j) (hj : j ∈ t) : a j = 1 ∨ a j = -1 :=
    (ha j).resolve_left (Finset.mem_filter.mp hj).2
  have hc : t.card = n := by
    have hsq : ∑ j ∈ s, a j ^ 2 = ∑ j ∈ t, a j ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hjs hjt
      have : a j = 0 := by simpa [t, hjs] using hjt
      simp [this]
    have hsum : ∑ j ∈ t, a j ^ 2 = (t.card : ℤ) := by
      calc
        _ = ∑ _j ∈ t, (1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro j hj
          rcases ht j hj with h | h <;> simp [h]
        _ = _ := by simp
    exact_mod_cast hsum.symm.trans (hsq.symm.trans hn)
  let e : Fin n ≃ {j // j ∈ t} := (finCongr hc.symm).trans t.equivFin.symm
  refine ⟨fun r => e r, fun i j h => e.injective (Subtype.ext h), ?_, ?_⟩
  · intro r
    exact ⟨(Finset.mem_filter.mp (e r).property).1, ht _ (e r).property⟩
  · intro M _ f hf
    have hs : ∑ j ∈ t, f j = ∑ j ∈ s, f j := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j hjs hjt
      apply hf
      simpa [t, hjs] using hjt
    rw [← hs, ← Finset.sum_attach]
    exact (Equiv.sum_comp e (fun j : {j // j ∈ t} => f j)).symm

variable {D : LocalData G} {k : TwistedModel ≃* D.centralizer}
  {I : SpecialInductionData D k} (E : IntegralExpansion I)

/-- Distinct signed nonprincipal coordinates in the complete irreducible basis. -/
public structure Frame (n : ℕ) where
  index : Fin n → E.Index
  injective : Function.Injective index
  nonprincipal : ∀ j, index j ≠ E.principalIndex
  sign : Fin n → ℤ
  sign_eq : ∀ j, sign j = 1 ∨ sign j = -1

namespace Frame
variable {E} {n : ℕ} (F : Frame E n)

@[expose] public def family : SignedFamily G n where
  character j := E.character (F.index j)
  irreducible j := E.irreducible (F.index j)
  injective := E.injective.comp F.injective
  nonprincipal j h := F.nonprincipal j (E.injective (h.trans E.principal_character.symm))
  sign := F.sign
  sign_eq := F.sign_eq

@[expose] public def coeff (i : Fin 5) (j : Fin n) : ℤ :=
  F.sign j * E.coefficient i (F.index j)

public theorem coeff_sq (i : Fin 5) (j : Fin n) :
    F.coeff i j ^ 2 = E.coefficient i (F.index j) ^ 2 := by
  rcases F.sign_eq j with h | h <;> simp [coeff, h]

public theorem coefficient_term (i : Fin 5) (j : Fin n) :
    (E.coefficient i (F.index j) : ℂ) • E.character (F.index j) =
      (F.coeff i j : ℂ) • F.family.term j := by
  rcases F.sign_eq j with h | h <;>
    simp [coeff, family, SignedFamily.term, h]

public theorem multiplicity (i : Fin 5) (j : Fin n) :
    scalarProduct G (I.induced i) (F.family.term j) = (F.coeff i j : ℂ) := by
  rw [SignedFamily.term, scalarProduct_smul_right, star_intCast]
  change scalarProduct G (I.induced i) (E.character (F.index j)) * (F.sign j : ℂ) = _
  rw [E.multiplicity]
  simp [coeff, mul_comm]

public theorem unit (hU : HasUnitMultiplicities I.induced) (i : Fin 5) (j : Fin n) :
    F.coeff i j = 0 ∨ F.coeff i j = 1 ∨ F.coeff i j = -1 := by
  have h := hU (E.character (F.index j)) (E.irreducible (F.index j)) i
  rw [E.multiplicity] at h
  have h' : E.coefficient i (F.index j) = 0 ∨ E.coefficient i (F.index j) = 1 ∨
      E.coefficient i (F.index j) = -1 := by exact_mod_cast h
  rcases F.sign_eq j with hs | hs <;> rcases h' with h | h | h <;> simp [coeff, hs, h]

@[expose] public def rest : Finset E.Index :=
  Finset.univ \ (insert E.principalIndex (Finset.univ.image F.index))

public theorem mem_rest (j : E.Index) :
    j ∈ F.rest ↔ j ≠ E.principalIndex ∧ ∀ r, F.index r ≠ j := by
  classical
  simp [rest]

public theorem split_sum {M : Type*} [AddCommMonoid M] (f : E.Index → M) :
    ∑ j, f j = f E.principalIndex + ∑ r, f (F.index r) + ∑ j ∈ F.rest, f j := by
  classical
  have hp : E.principalIndex ∉ Finset.univ.image F.index := by
    simpa using F.nonprincipal
  have h := Finset.sum_sdiff (f := f)
    (Finset.subset_univ (insert E.principalIndex (Finset.univ.image F.index)))
  rw [Finset.sum_insert hp, Finset.sum_image (fun i _ j _ he => F.injective he)] at h
  simpa only [rest, add_comm, add_left_comm, add_assoc] using h.symm

public theorem norm_rest (i : Fin 5) :
    (exceptionalCoefficients i 0) ^ 2 + ∑ r, F.coeff i r ^ 2 +
      ∑ j ∈ F.rest, E.coefficient i j ^ 2 = exceptionalGram i i := by
  rw [← E.norm_sq, F.split_sum (fun j => E.coefficient i j ^ 2), E.principal_coefficient]
  simp only [coeff_sq]

public theorem norm_le (i : Fin 5) :
    (exceptionalCoefficients i 0) ^ 2 + ∑ r, F.coeff i r ^ 2 ≤ exceptionalGram i i := by
  have h := F.norm_rest i
  have hpos : 0 ≤ ∑ j ∈ F.rest, E.coefficient i j ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  omega

/-- Exhaust all unused nonprincipal coordinates and append their signed terms. -/
public theorem extend (hU : HasUnitMultiplicities I.induced) (i : Fin 5) (m : ℕ)
    (hm : ∑ j ∈ F.rest, E.coefficient i j ^ 2 = (m : ℤ)) :
    ∃ H : Frame E (n + m),
      (∀ r, H.family.term (Fin.castAdd m r) = F.family.term r) ∧
      I.induced i = (exceptionalCoefficients i 0 : ℂ) • (1 : ClassFunction G) +
        ∑ r, (F.coeff i r : ℂ) • F.family.term r +
        ∑ r : Fin m, H.family.term (Fin.natAdd n r) := by
  classical
  have hu (j) : E.coefficient i j = 0 ∨ E.coefficient i j = 1 ∨ E.coefficient i j = -1 := by
    have h := hU (E.character j) (E.irreducible j) i
    rw [E.multiplicity] at h
    exact_mod_cast h
  obtain ⟨p, hp, hs, he⟩ := enumerate_support F.rest (E.coefficient i) hu m hm
  let H : Frame E (n + m) := {
    index := Fin.append F.index p
    injective := Fin.append_injective_iff.mpr ⟨F.injective, hp,
      fun r s => ((F.mem_rest _).mp (hs s).1).2 r⟩
    nonprincipal := by
      intro r
      refine Fin.addCases (fun j => ?_) (fun j => ?_) r
      · simpa using F.nonprincipal j
      · simpa using ((F.mem_rest _).mp (hs j).1).1
    sign := Fin.append F.sign (fun r => E.coefficient i (p r))
    sign_eq := by
      intro r
      refine Fin.addCases (fun j => ?_) (fun j => ?_) r
      · simpa using F.sign_eq j
      · simpa using (hs j).2 }
  refine ⟨H, ?_, ?_⟩
  · intro r
    simp [H, family, SignedFamily.term]
  · rw [E.expansion, F.split_sum, E.principal_coefficient, E.principal_character]
    congr 1
    · simp only [coefficient_term]
    · rw [he (fun j => (E.coefficient i j : ℂ) • E.character j) (by intros; simp_all)]
      simp [H, family, SignedFamily.term]

/-- When the selected coordinates use the entire norm, the expansion is complete. -/
public theorem expansion_of_norm_eq (hU : HasUnitMultiplicities I.induced) (i : Fin 5)
    (h : (exceptionalCoefficients i 0) ^ 2 + ∑ r, F.coeff i r ^ 2 = exceptionalGram i i) :
    I.induced i = (exceptionalCoefficients i 0 : ℂ) • (1 : ClassFunction G) +
      ∑ r, (F.coeff i r : ℂ) • F.family.term r := by
  have hn := F.norm_rest i
  obtain ⟨_, _, he⟩ := F.extend hU i 0 (by omega)
  simpa using he

@[expose] public def reindex (e : Fin n ≃ Fin n) : Frame E n where
  index := F.index ∘ e
  injective := F.injective.comp e.injective
  nonprincipal j := F.nonprincipal (e j)
  sign := F.sign ∘ e
  sign_eq j := F.sign_eq (e j)

public theorem reindex_term (e : Fin n ≃ Fin n) (j : Fin n) :
    (F.reindex e).family.term j = F.family.term (e j) := rfl

public theorem reindex_coeff (e : Fin n ≃ Fin n) (i : Fin 5) (j : Fin n) :
    (F.reindex e).coeff i j = F.coeff i (e j) := rfl

end Frame
end SignedAnalysis.DecompositionSupports
end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
