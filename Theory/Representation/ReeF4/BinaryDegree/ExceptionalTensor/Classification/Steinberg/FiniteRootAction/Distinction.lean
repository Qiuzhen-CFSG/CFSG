module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Distinction.TorusCharacters
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.Distinction.DigitRecovery
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.OrdinaryComparison
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.SourceHighestWeight

/-!
# Distinction of the actual finite Ree exceptional tensors

A finite equivalence preserves the line fixed by all native positive elements.
The two genuine fixed tori then give equal highest characters. The native
orbit-Weyl words detect which digit columns vanish, resolving the zero/full
ambiguity in those characters. Polynomial uniqueness over the coefficient
field recovers each ordinary binary digit. The actual tensor permutation and
source algebraic highest-weight uniqueness recover equivalence of every
original exceptional basic factor.

This discharges the finite parameter-distinction clause of Steinberg (1963),
5.1(4) and 12.2, on the literal Model action, including q=2. Universality of
the algebraic F4 carrier is the only independent geometric input.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
open Theory.AlgebraicGroup AlgebraicTensor Distinction
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]

omit [IsAlgClosed F] [CharP F 2] in
private theorem equiv_action {G V W : Type*} [Monoid G] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] {ρ : Representation F G V} {σ : Representation F G W}
    (e : Representation.Equiv ρ σ) (g : G) (v : V) :
    e.toLinearEquiv (ρ g v) = σ g (e.toLinearEquiv v) := by
  exact Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g v

omit [IsAlgClosed F] [CharP F 2] in
private theorem equiv_fixed_iff {G V W : Type*} [Monoid G] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] {ρ : Representation F G V} {σ : Representation F G W}
    (e : Representation.Equiv ρ σ) (v : V) (w : W) (a : F) (ha : a≠0)
    (he : e.toLinearEquiv v = a • w) (g : G) : ρ g v = v ↔ σ g w = w := by
  rw [←e.toLinearEquiv.injective.eq_iff, equiv_action, he, map_smul]
  exact (smul_right_injective W ha).eq_iff

omit [IsAlgClosed F] [CharP F 2] in
private theorem equiv_eigenvalue {G V W : Type*} [Monoid G] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] {ρ : Representation F G V} {σ : Representation F G W}
    (e : Representation.Equiv ρ σ) (v : V) (w : W) (hw : w≠0) (a : F) (ha : a≠0)
    (he : e.toLinearEquiv v = a • w) (g : G) (x y : F)
    (hx : ρ g v = x • v) (hy : σ g w = y • w) : x=y := by
  have hh := equiv_action e g v
  rw [hx,map_smul,he,map_smul,hy,smul_smul,smul_smul] at hh
  have hxy := smul_left_injective F hw hh
  exact mul_right_cancel₀ ha (by simpa only [mul_comm a y] using hxy)

theorem ordinary_equiv_basic_weights (m : ℕ) (B C : ZMod (2*m+1) → AlgebraicFactor F)
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (q : ∀i, RootExpansion (basicFactor m C i).action)
    (b c : ℕ → BasicWeight) (v : ∀i, (basicFactor m B i).Space)
    (w : ∀i, (basicFactor m C i).Space)
    (hv : ∀i, (basicFactor m B i).IsBasicHighestWeightVector (b i) (v i))
    (hw : ∀i, (basicFactor m C i).IsBasicHighestWeightVector (c i) (w i))
    (f : CoefficientField m →+* F)
    (e : Representation.Equiv (ordinaryAction m B f (2*m+1)) (ordinaryAction m C f (2*m+1))) :
    ∀i<2*m+1, b i = c i := by
  obtain ⟨a,ha,he⟩ := equiv_highest_tensor m B C hU q b c v w hv hw f e
  have hn := highestTensor_ne_zero m C w (fun i => (hw i).1) (2*m+1)
  have hd (s : LargeLocalSeeds.Side) : ∀i<2*m+1, sideDigit s (b i)=sideDigit s (c i) := by
    apply side_digits_of_characters m f b c s
    · intro t
      exact equiv_eigenvalue e _ _ hn a ha he (sideTorusElement m s t) _ _
        (sideTorusElement_highest m B b v hv f _ s t)
        (sideTorusElement_highest m C c w hw f _ s t)
    · rw [←sideElement_fixes_highest_iff m B b v hv f _ s,
        ←sideElement_fixes_highest_iff m C c w hw f _ s]
      exact equiv_fixed_iff e _ _ a ha he (sideElement m s)
  intro i hi
  apply Prod.ext <;> apply Fin.ext
  · exact hd .suzuki i hi
  · exact hd .linear i hi

theorem exceptionalTensor_equivalent_factors (m : ℕ)
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (B C : ZMod (2*m+1) → AlgebraicFactor F)
    (hB : ∀i,(B i).IsExceptionalBasic) (hC : ∀i,(C i).IsExceptionalBasic)
    (f : CoefficientField m →+* F)
    (h : Nonempty (Representation.Equiv (exceptionalTensor (splitEmbedding f) B).ρ
      (exceptionalTensor (splitEmbedding f) C).ρ)) :
    ∀i, AreEquivalentRepresentations (B i).action (C i).action := by
  classical
  choose b v hv using fun i : ℕ => hB (ordinaryIndex m (i : ZMod (2*m+1)))
  choose c w hw using fun i : ℕ => hC (ordinaryIndex m (i : ZMod (2*m+1)))
  let q : ∀i, RootExpansion (basicFactor m C i).action := fun i =>
    Classical.choice (rootExpansion_nonempty (basicFactor m C i).action (basicFactor m C i).irreducible.1)
  obtain ⟨eB⟩ := ordinaryAction_equiv_exceptionalTensor m B f
  obtain ⟨eC⟩ := ordinaryAction_equiv_exceptionalTensor m C f
  obtain ⟨e⟩ := h
  have hd := ordinary_equiv_basic_weights m B C hU q b c v w hv hw f (eB.trans (e.trans eC.symm))
  intro i
  let j := (ordinaryIndex m).symm i
  have hj : ordinaryIndex m (j.val : ZMod (2*m+1)) = i := by
    rw [ZMod.natCast_zmod_val]
    exact (ordinaryIndex m).apply_symm_apply i
  have hfact := SourceHighestWeight.equivalent_of_same_basicHighestWeight
    (basicFactor m B j.val) (basicFactor m C j.val) (b j.val) ⟨v j.val,hv j.val⟩
    ⟨w j.val, by rw [hd j.val j.val_lt]; exact hw j.val⟩
  change AreEquivalentRepresentations (B (ordinaryIndex m (j.val : ZMod (2*m+1)))).action
    (C (ordinaryIndex m (j.val : ZMod (2*m+1)))).action at hfact
  rw [hj] at hfact
  exact hfact

/-- The exact coefficient embedding in the B.4 finite tensor consumer needs no
additional parameter-distinction premise. -/
theorem exceptionalTensor_distinction (m : ℕ)
    (hU : IsUniversalVersion (F4Chevalley.Carrier (k := F)))
    (B C : ZMod (2*m+1) → AlgebraicFactor F)
    (hB : ∀i,(B i).IsExceptionalBasic) (hC : ∀i,(C i).IsExceptionalBasic)
    (h : Nonempty (Representation.Equiv
      (exceptionalTensor (splitEmbedding (coefficientHom F m)) B).ρ
      (exceptionalTensor (splitEmbedding (coefficientHom F m)) C).ρ)) :
    ∀i, AreEquivalentRepresentations (B i).action (C i).action :=
  exceptionalTensor_equivalent_factors m hU B C hB hC (coefficientHom F m) h

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
