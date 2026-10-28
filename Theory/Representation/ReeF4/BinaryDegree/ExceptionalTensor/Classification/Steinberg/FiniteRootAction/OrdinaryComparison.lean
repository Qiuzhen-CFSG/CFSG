module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.OrdinaryComparison.TensorPermutation
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.CoefficientFrobenius
public import Theory.Representation.RepEquiv

/-!
# Ordinary and exceptional tensors on the original finite Ree group

On an actual Ree fixed point, exceptional powers reduce modulo `2*m+1`,
and exceptional power `2*i` equals ordinary Frobenius power `i`. Consequently
the ordinary factor in position `i` is the exceptional factor at index `2*i`.
The proved cyclic permutation of these indices reorders the full tensor by
an actual intertwining equivalence. Irreducibility thus transports to the
literal exceptional tensor used by the classification consumer.

Source: GLS3 Definition 2.8.3 and Remark 2.8.4; Steinberg (1963), Section 12.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
open Theory.AlgebraicGroup
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

private theorem frobenius_pow_splitEmbedding (m : ℕ) (f : CoefficientField m →+* F)
    (x : SplitGroup m) (i : ℕ) :
    (Geometry.frobeniusEnd ^ i) (splitEmbedding f x) =
      splitEmbedding f ((splitFrobeniusEnd m ^ i) x) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ', pow_succ']
    change Geometry.frobeniusEnd ((Geometry.frobeniusEnd ^ i) (splitEmbedding f x)) =
      splitEmbedding f (splitFrobeniusEnd m ((splitFrobeniusEnd m ^ i) x))
    rw [ih, Geometry.frobeniusEnd_splitEmbedding]

private theorem ordinary_factor_eq (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F) (f : CoefficientField m →+* F) (i : ℕ) :
    ((basicFactor m B i).restrict ((Geometry.frobeniusEnd ^ i).comp (modelEmbedding f))).ρ =
      (exceptionalFactor (splitEmbedding f) B (ordinaryIndex m (i : ZMod (2 * m + 1)))).ρ := by
  ext g v
  change ((B _).action.action ((Geometry.frobeniusEnd ^ i)
    (splitEmbedding f (toSplitGroup m g)))).val v = _
  rw [frobenius_pow_splitEmbedding, ← exceptionalEndomorphism_sq, ← pow_mul]
  have hi : ordinaryIndex m (i : ZMod (2 * m + 1)) = ((2 * i : ℕ) : ZMod (2 * m + 1)) := by
    simp only [ordinaryIndex_apply, Nat.cast_mul, Nat.cast_ofNat]
  change ((B _).action.action (splitEmbedding f ((exceptionalEndomorphism m ^ (2 * i))
    (toSplitGroup m g)))).val v = ((B _).action.action (splitEmbedding f
      ((exceptionalEndomorphism m ^ (ordinaryIndex m (i : ZMod (2 * m + 1))).val)
        (toSplitGroup m g)))).val v
  have hp : (exceptionalEndomorphism m ^ (ordinaryIndex m (i : ZMod (2 * m + 1))).val)
      (toSplitGroup m g) = (exceptionalEndomorphism m ^ (2 * i)) (toSplitGroup m g) := by
    rw [hi, CoefficientFrobenius.exceptional_pow_val]
  rw [hp]

private theorem cyclic_factors_perm (m : ℕ) {A : Type*}
    (V : ZMod (2 * m + 1) → A) :
    ((List.range (2 * m + 1)).map (fun i : ℕ => V (ordinaryIndex m (i : ZMod (2 * m + 1))))).Perm
      ((List.range (2 * m + 1)).map (fun i : ℕ => V (i : ZMod (2 * m + 1)))) := by
  let e := (ZMod.finEquiv (2 * m + 1)).toEquiv
  let σ : Equiv.Perm (Fin (2 * m + 1)) := e.trans ((ordinaryIndex m).trans e.symm)
  have h := Equiv.Perm.ofFn_comp_perm σ (fun i => V (e i))
  have hcast (i : Fin (2 * m + 1)) : e i = (i.val : ZMod (2 * m + 1)) := by
    exact (ZMod.natCast_zmod_val (e i)).symm
  have hof (f : ℕ → A) : List.ofFn (fun i : Fin (2 * m + 1) => f i.val) =
      (List.range (2 * m + 1)).map f := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  have hfun : (fun i => V (e i)) ∘ σ =
      (fun i : Fin (2 * m + 1) => V (ordinaryIndex m (i.val : ZMod (2 * m + 1)))) := by
    funext i
    change V (e (e.symm (ordinaryIndex m (e i)))) = _
    rw [e.apply_symm_apply, hcast]
  rw [hfun] at h
  simp only [hcast] at h
  rw [hof (fun i => V (ordinaryIndex m (i : ZMod (2 * m + 1)))),
    hof (fun i => V (i : ZMod (2 * m + 1)))] at h
  exact h

/-- The actual ordinary tensor is the exceptional tensor with its factors
permuted by the ordinary-index permutation. -/
theorem ordinaryAction_equiv_exceptionalTensor (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F) (f : CoefficientField m →+* F) :
    Nonempty (Representation.Equiv (ordinaryAction m B f (2 * m + 1))
      (exceptionalTensor (splitEmbedding f) B).ρ) := by
  let V : ℕ → FDRep F (Model m) := fun i =>
    (basicFactor m B i).restrict ((Geometry.frobeniusEnd ^ i).comp (modelEmbedding f))
  let W : ℕ → FDRep F (Model m) := fun i =>
    exceptionalFactor (splitEmbedding f) B (ordinaryIndex m (i : ZMod (2 * m + 1)))
  obtain ⟨e₁⟩ := tensorPrefix_equiv_of_factors V W (2 * m + 1) (fun i _ => by
    have h := ordinary_factor_eq m B f i
    exact ⟨Representation.Equiv.mk (LinearEquiv.refl F _) (fun g => by
      change (V i).ρ g = (W i).ρ g
      exact DFunLike.congr_fun h g)⟩)
  obtain ⟨e₂⟩ := tensorPrefix_equiv_of_list_perm W
    (fun i => exceptionalFactor (splitEmbedding f) B (i : ZMod (2 * m + 1)))
    (2 * m + 1) (cyclic_factors_perm m (exceptionalFactor (splitEmbedding f) B))
  exact ⟨(ordinaryAction_equiv_tensorPrefix m B f (2 * m + 1)).trans (e₁.trans e₂)⟩

/-- Irreducibility proved on the filtered ordinary tensor is exactly the
literal exceptional-tensor irreducibility required by the source consumer. -/
theorem exceptionalTensor_isIrreducible_of_ordinary (m : ℕ)
    (B : ZMod (2 * m + 1) → AlgebraicFactor F) (f : CoefficientField m →+* F)
    (h : Representation.IsIrreducible (ordinaryAction m B f (2 * m + 1))) :
    Representation.IsIrreducible (exceptionalTensor (splitEmbedding f) B).ρ := by
  obtain ⟨e⟩ := ordinaryAction_equiv_exceptionalTensor m B f
  exact (Representation.RepEquiv.ofRepresentationEquiv e.symm).irreducible_of_euqiv h

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
