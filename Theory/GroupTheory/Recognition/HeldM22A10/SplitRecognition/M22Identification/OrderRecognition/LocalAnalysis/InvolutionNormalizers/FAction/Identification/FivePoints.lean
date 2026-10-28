module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.FAction.Identification.Data

/-!
# The faithful action on the five lines of a spread

For each canonical generator, 120 short words give distinct automorphisms.
If they belong to a group of order 120, they exhaust that group. Their
matrices permute five explicitly labelled triples of nonzero vectors,
and only the identity fixes all five triples. The resulting faithful
homomorphism to S5 is bijective by equality of orders.

Source: the finite identification step in Janko, J. Algebra 9 (1968),
Section 2, proof of Lemma 2, pp.4–5.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.FAction.Identification

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_eval : ∀ (k : Fin 2) (i : Fin 120),
    evalMat (seeds k) (repWords k i) = table k i := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_injective : ∀ k : Fin 2, Function.Injective (table k) := by decide +kernel

private def permMap (k : Fin 2) (i : Fin 120) (j : Fin 5) : Fin 5 :=
  label k (act (table k i) (lineRep j))

private theorem label_lineRep : ∀ (k : Fin 2) (j : Fin 5),
    label k (lineRep j) = j := by decide +kernel

private theorem lineRep_ne_zero : ∀ j : Fin 5, lineRep j ≠ 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_action : ∀ (k : Fin 2) (i : Fin 120) (v : Fin 16), v ≠ 0 →
    label k (act (table k i) v) = permMap k i (label k v) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem permMap_bijective : ∀ (k : Fin 2) (i : Fin 120),
    Function.Bijective (permMap k i) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_faithful : ∀ (k : Fin 2) (i : Fin 120),
    (∀ j : Fin 5, permMap k i j = j) → table k i = basisIndex := by decide +kernel

private noncomputable def tablePerm (k : Fin 2) (i : Fin 120) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (permMap k i) (permMap_bijective k i)

/-- Either canonical generator, together with the local actors, yields an actual S5
isomorphism for any containing automorphism group of order 120. -/
public theorem identification_of_seed (H : Subgroup (MulAut modelF))
    (hlocal : localAutomizer ≤ H) (hcard : Nat.card H = 120)
    (f : MulAut modelF) (hf : f ∈ H) (k : Fin 2) (hk : matrix f = seeds k) :
    Nonempty (H ≃* Equiv.Perm (Fin 5)) := by
  classical
  let : Finite H := Nat.finite_of_card_ne_zero (hcard ▸ (by decide))
  let reps : Fin 120 → H := fun i =>
    ⟨evalAut f (repWords k i), evalAut_mem H hlocal f hf _⟩
  have reps_matrix (i : Fin 120) : matrix (reps i) = table k i := by
    change matrix (evalAut f (repWords k i)) = _
    rw [matrix_evalAut, hk, table_eval]
  have reps_inj : Function.Injective reps := by
    intro i j he
    apply table_injective k
    rw [← reps_matrix i, ← reps_matrix j, he]
  have reps_bij : Function.Bijective reps :=
    (Nat.bijective_iff_injective_and_card reps).mpr
      ⟨reps_inj, by rw [Nat.card_fin, hcard]⟩
  let e : Fin 120 ≃ H := Equiv.ofBijective reps reps_bij
  have index_matrix (g : H) : matrix g = table k (e.symm g) := by
    rw [← reps_matrix]
    exact congrArg (fun a : H => matrix (a : MulAut modelF)) (e.apply_symm_apply g).symm
  let rho : H → Equiv.Perm (Fin 5) := fun g => tablePerm k (e.symm g)
  have rho_spec (g : H) (v : Fin 16) (hv : v ≠ 0) :
      rho g (label k v) = label k (act (matrix g) v) := by
    change permMap k (e.symm g) (label k v) = _
    rw [index_matrix]
    exact (table_action k (e.symm g) v hv).symm
  have nonzero (g : H) (v : Fin 16) (hv : v ≠ 0) :
      act (matrix g) v ≠ 0 := fun he => hv (matrix_nonsingular g v he)
  have comp (g h : H) (v : Fin 16) :
      act (matrix ((g * h : H) : MulAut modelF)) v =
        act (matrix g) (act (matrix h) v) := by
    apply word_injective
    rw [← matrix_action, ← matrix_action, ← matrix_action]
    rfl
  let hom : H →* Equiv.Perm (Fin 5) :=
    { toFun := rho
      map_one' := by
        apply Equiv.ext
        intro j
        rw [← label_lineRep k j, rho_spec 1 (lineRep j) (lineRep_ne_zero j)]
        have he : act (matrix (1 : MulAut modelF)) (lineRep j) = lineRep j := by
          apply word_injective
          rw [← matrix_action]
          rfl
        exact congrArg (label k) he
      map_mul' := by
        intro g h
        apply Equiv.ext
        intro j
        change rho (g * h) j = rho g (rho h j)
        rw [← label_lineRep k j, rho_spec (g * h) (lineRep j) (lineRep_ne_zero j),
          rho_spec h (lineRep j) (lineRep_ne_zero j),
          rho_spec g _ (nonzero h _ (lineRep_ne_zero j)), comp] }
  have hinj : Function.Injective hom := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_antisymm ?_ bot_le
    intro g hg
    change g = 1
    have he : ∀ j : Fin 5, permMap k (e.symm g) j = j := by
      intro j
      exact congrArg (fun a : Equiv.Perm (Fin 5) => a j) hg
    apply Subtype.ext
    apply matrix_injective
    change matrix (g : MulAut modelF) = matrix (1 : MulAut modelF)
    rw [index_matrix, matrix_one]
    exact table_faithful k (e.symm g) he
  have hsize : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  exact ⟨MulEquiv.ofBijective hom ((Nat.bijective_iff_injective_and_card hom).mpr
    ⟨hinj, hcard.trans hsize.symm⟩)⟩

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.FAction.Identification
