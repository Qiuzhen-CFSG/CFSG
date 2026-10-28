module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Embedding
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.FrobeniusReduction
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Weights

/-!
# Root, highest-weight, and tensor interfaces for exceptional restriction

The root formula of an algebraic exceptional endomorphism determines its
restriction to the embedded finite split group. Induction gives compatibility
with every power. The embedded Ree group is exactly the intersection of this
split image with the algebraic fixed points. Identifying it with *all* fixed
points still requires a rational-point descent theorem.

The tensor bridge restricts an equivalence on the full algebraic point group
to the existing concrete `exceptionalTensor`. `HasHighestWeight` extends the
published basic predicate to arbitrary nonnegative simple-coroot coefficients;
its basic specialization is definitionally the same predicate.

Sources: GLS3, Definition 2.8.1, Remark 2.8.4, and the proof of Corollary
2.8.6(b); Steinberg, *Endomorphisms of Linear Algebraic Groups*, §13. The
endomorphism's existence, algebraic tensor irreducibility, highest-weight
classification, and finite restriction theorem are not asserted here.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg
universe u v
variable {F : Type u} [Field F] [IsAlgClosed F] {k : ℕ}

/-- Points of the actual closed F₄ Chevalley carrier. -/
abbrev PointGroup (F : Type u) [Field F] [IsAlgClosed F] :=
  Variety.Point (F4Chevalley.Carrier (k := F))

/-- Restrict the proved coefficient embedding to the concrete Ree fixed group. -/
@[expose] noncomputable def modelEmbedding (f : CoefficientField k →+* F) : Model k →* PointGroup F :=
  (splitEmbedding f).comp (toSplitGroup k)

theorem modelEmbedding_injective (f : CoefficientField k →+* F) :
    Function.Injective (modelEmbedding f) :=
  (splitEmbedding_injective f).comp (toSplitGroup_injective k)

/-- The actual long/short root formula; no existence is asserted here. -/
@[expose] def HasExceptionalRootFormula (ψ : Monoid.End (PointGroup F)) : Prop :=
  ∀ (r : F4Chevalley.Root) (t : F), ψ (algebraicRootElement r t) =
    algebraicRootElement (exceptionalRootPermutation r) (exceptionalParameter r t)

theorem exceptional_comp_splitEmbedding (f : CoefficientField k →+* F)
    (ψ : Monoid.End (PointGroup F)) (hψ : HasExceptionalRootFormula ψ) :
    ψ.comp (splitEmbedding f) = (splitEmbedding f).comp (exceptionalEndomorphism k) := by
  apply splitGroup_hom_ext
  intro r t
  change ψ (splitEmbedding f (rootGeneratorInGroup k r t)) =
    splitEmbedding f (exceptionalEndomorphism k (rootGeneratorInGroup k r t))
  rw [splitEmbedding_rootGenerator, hψ, exceptionalEndomorphism_rootGenerator,
    splitEmbedding_rootGenerator]
  congr 1
  by_cases hr : IsLongRoot r
  · rw [exceptionalParameter_of_long hr, exceptionalParameter_of_long hr]
  · rw [exceptionalParameter_of_short hr, exceptionalParameter_of_short hr, map_pow]

theorem exceptional_pow_splitEmbedding (f : CoefficientField k →+* F)
    (ψ : Monoid.End (PointGroup F)) (hψ : HasExceptionalRootFormula ψ)
    (n : ℕ) (x : SplitGroup k) :
    (ψ ^ n) (splitEmbedding f x) = splitEmbedding f ((exceptionalEndomorphism k ^ n) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ']
    change ψ ((ψ ^ n) _) = splitEmbedding f (exceptionalEndomorphism k (_))
    rw [ih]
    exact DFunLike.congr_fun (exceptional_comp_splitEmbedding f ψ hψ) _

theorem modelEmbedding_fixed (f : CoefficientField k →+* F)
    (ψ : Monoid.End (PointGroup F)) (hψ : HasExceptionalRootFormula ψ) (x : Model k) :
    (ψ ^ (2 * k + 1)) (modelEmbedding f x) = modelEmbedding f x := by
  change (ψ ^ (2 * k + 1)) (splitEmbedding f (toSplitGroup k x)) = _
  rw [exceptional_pow_splitEmbedding f ψ hψ, ← reeTwist_eq_pow, reeTwist_toSplitGroup]
  rfl

/-- The exceptional tensor on the full algebraic point group. -/
@[expose] noncomputable def pointTensor (ψ : Monoid.End (PointGroup F))
    (B : ZMod (2 * k + 1) → AlgebraicFactor F) : FDRep F (PointGroup F) :=
  tensorPrefix (fun i : ℕ => (B (i : ZMod (2 * k + 1))).restrict
    (ψ ^ (i : ZMod (2 * k + 1)).val)) (2 * k + 1)

theorem exceptionalFactor_eq_pullback (f : CoefficientField k →+* F)
    (ψ : Monoid.End (PointGroup F)) (hψ : HasExceptionalRootFormula ψ)
    (B : ZMod (2 * k + 1) → AlgebraicFactor F) (i : ZMod (2 * k + 1)) :
    (exceptionalFactor (splitEmbedding f) B i).ρ =
      ((B i).restrict (ψ ^ i.val)).ρ.comp (modelEmbedding f) := by
  ext g v
  change ((B i).action.action (splitEmbedding f ((exceptionalEndomorphism k ^ i.val)
    (toSplitGroup k g)))).val v = ((B i).action.action ((ψ ^ i.val)
      (splitEmbedding f (toSplitGroup k g)))).val v
  rw [exceptional_pow_splitEmbedding f ψ hψ]

theorem equivalent_restrict {B C : AlgebraicFactor F}
    (h : AreEquivalentRepresentations B.action C.action)
    {G : Type v} [Group G] (ι : G →* PointGroup F) :
    Nonempty (Representation.Equiv (B.restrict ι).ρ (C.restrict ι).ρ) := by
  obtain ⟨e, he⟩ := h
  exact ⟨Representation.Equiv.mk e (fun g => LinearMap.ext (he (ι g)))⟩


/-- Restriction of an intertwining equivalence along a group homomorphism. -/
noncomputable def pullbackEquiv {G H : Type*} [Group G] [Group H]
    {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {ρ : Representation F G V} {σ : Representation F G W}
    (e : Representation.Equiv ρ σ) (f : H →* G) :
    Representation.Equiv (ρ.comp f) (σ.comp f) :=
  .mk e.toLinearEquiv (fun g => e.toIntertwiningMap.2 (f g))

private noncomputable def tensorEquiv {G : Type*} [Group G]
    {V W X Y : Type*}
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
    {ρ : Representation F G V} {σ : Representation F G W}
    {τ : Representation F G X} {π : Representation F G Y}
    (e : Representation.Equiv ρ σ) (f : Representation.Equiv τ π) :
    Representation.Equiv (ρ.tprod τ) (σ.tprod π) :=
  .mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv)
    (e.toIntertwiningMap.tensor f.toIntertwiningMap).2

/-- Restriction commutes with the concrete iterated tensor construction. -/
noncomputable def tensorPrefix_pullbackEquiv {G H : Type*} [Group G] [Group H]
    (V : ℕ → FDRep F G) (f : H →* G) (n : ℕ) :
    Representation.Equiv ((tensorPrefix V n).ρ.comp f)
      (tensorPrefix (fun i => FDRep.of ((V i).ρ.comp f)) n).ρ := by
  induction n with
  | zero => exact Representation.Equiv.refl _
  | succ n ih =>
    change Representation.Equiv
      (Representation.tprod ((tensorPrefix V n).ρ.comp f) ((V n).ρ.comp f))
      (Representation.tprod
        (tensorPrefix (fun i => FDRep.of ((V i).ρ.comp f)) n).ρ ((V n).ρ.comp f))
    exact tensorEquiv ih (Representation.Equiv.refl ((V n).ρ.comp f))

theorem pointTensor_pullback (f : CoefficientField k →+* F)
    (ψ : Monoid.End (PointGroup F)) (hψ : HasExceptionalRootFormula ψ)
    (B : ZMod (2 * k + 1) → AlgebraicFactor F) :
    Nonempty (Representation.Equiv ((pointTensor ψ B).ρ.comp (modelEmbedding f))
      (exceptionalTensor (splitEmbedding f) B).ρ) := by
  let V : ℕ → FDRep F (PointGroup F) := fun i =>
    (B (i : ZMod (2 * k + 1))).restrict (ψ ^ (i : ZMod (2 * k + 1)).val)
  have hV : (fun i => FDRep.of ((V i).ρ.comp (modelEmbedding f))) =
      (fun i : ℕ => exceptionalFactor (splitEmbedding f) B (i : ZMod (2 * k + 1))) := by
    funext i
    have hi := exceptionalFactor_eq_pullback f ψ hψ B (i : ZMod (2 * k + 1))
    exact congrArg (fun ρ : Representation F (Model k) (B (i : ZMod (2 * k + 1))).Space =>
      FDRep.of ρ) hi.symm
  have e := tensorPrefix_pullbackEquiv V (modelEmbedding f) (2 * k + 1)
  rw [hV] at e
  exact ⟨e⟩

theorem factor_restrict_equiv_tensor (f : CoefficientField k →+* F)
    (ψ : Monoid.End (PointGroup F)) (hψ : HasExceptionalRootFormula ψ)
    (B : ZMod (2 * k + 1) → AlgebraicFactor F) (A : AlgebraicFactor F)
    (h : Nonempty (Representation.Equiv (A.restrict (MonoidHom.id _)).ρ
      (pointTensor ψ B).ρ)) :
    Nonempty (Representation.Equiv (A.restrict (modelEmbedding f)).ρ
      (exceptionalTensor (splitEmbedding f) B).ρ) := by
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := pointTensor_pullback f ψ hψ B
  exact ⟨(pullbackEquiv e (modelEmbedding f)).trans e'⟩


/-- A specified dominant highest weight for the actual root and coroot actions. -/
@[expose] def HasHighestWeight (B : AlgebraicFactor F) (a : Weight) : Prop :=
  ∃ v : B.Space, v ≠ 0 ∧
    (∀ r : F4Chevalley.Root, typeF4RootPairing_base.IsPos r → ∀ t : F,
      (B.action.action (algebraicRootElement r t) : Module.End F B.Space) v = v) ∧
    (∀ (i : Fin 4) (t : Fˣ),
      (B.action.action (algebraicCorootElement (typeF4SimpleRootIndex i) t) :
        Module.End F B.Space) v = ((t : F) ^ a i) • v)

theorem hasHighestWeight_basic_iff (B : AlgebraicFactor F) (b : BasicWeight) :
    HasHighestWeight B (basicCoefficient b) ↔ HasBasicHighestWeight B b := Iff.rfl

theorem hasHighestWeight_of_equivalent {B C : AlgebraicFactor F} {a : Weight}
    (h : AreEquivalentRepresentations B.action C.action) (ha : HasHighestWeight B a) :
    HasHighestWeight C a := by
  obtain ⟨e, he⟩ := h
  obtain ⟨v, hv, hpos, htor⟩ := ha
  refine ⟨e v, by simpa using hv, ?_, ?_⟩
  · intro r hr t
    exact (he _ v).symm.trans (congrArg e (hpos r hr t))
  · intro i t
    exact (he _ v).symm.trans ((congrArg e (htor i t)).trans (map_smul e _ _))


theorem mem_modelEmbedding_range (f : CoefficientField k →+* F)
    (ψ : Monoid.End (PointGroup F)) (hψ : HasExceptionalRootFormula ψ) (y : PointGroup F) :
    y ∈ (modelEmbedding f).range ↔
      y ∈ (splitEmbedding f).range ∧ (ψ ^ (2 * k + 1)) y = y := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨toSplitGroup k x, rfl⟩, modelEmbedding_fixed f ψ hψ x⟩
  · rintro ⟨⟨x, rfl⟩, hx⟩
    have hfix : reeTwist k x = x := by
      apply splitEmbedding_injective f
      rw [reeTwist_eq_pow, ← exceptional_pow_splitEmbedding f ψ hψ]
      exact hx
    refine ⟨⟨x, (mem_fixedSubgroup k x).mpr hfix⟩, ?_⟩
    simp only [modelEmbedding, MonoidHom.comp_apply, toSplitGroup_apply]

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg
