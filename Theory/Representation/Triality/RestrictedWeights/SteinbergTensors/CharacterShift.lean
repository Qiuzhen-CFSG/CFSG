module
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.LeftWeights.Coefficient
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.LeftWeights.Graph
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.CharacterPeriod
/-!
# Actual Frobenius trace shift and tensor character periods

Highest-weight uniqueness supplies coefficient-Frobenius and graph intertwiners
for every actual basic factor. Tensor traces multiply, and the fixed-point
equation turns exponent overflow into the inverse graph action. A cyclic product
therefore proves the exact forward shift of the wrapped weight sequence.
Finite irreducibility and parameter separation then identify character periods
with weight periods. Those finite inputs are supplied by the separate checked
restriction theorem; no coefficient-twist or trace identity is assumed there.
Source: GLS3 2.8.3–4 and 2.8.8, with the original graph-then-field convention.
-/

@[expose] public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.CoefficientTransport
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
open AlgebraicTensor

def basicCharacter (A : BasicWeight → RationalFactor K) (a : BasicWeight) (g : K.Point) : k :=
  Representation.character ((A a).restrict (MonoidHom.id _)).ρ g

theorem basicCharacter_frobenius (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding) (a : BasicWeight)
    (g : K.Point) : basicCharacter A.factor a (F.morphism.onPoints g) =
      basicCharacter A.factor a g ^ 2 := by
  let b := Module.finBasis k (A.factor a).Space
  have he := congrFun (Representation.char_iso (leftCoefficientFrobeniusEquiv S F A a b)) g
  have ht := Representation.character_semilinearConjugate (frobeniusEquiv k 2)
    ((A.factor a).restrict (MonoidHom.id _)).ρ
    (basisCoefficientEquiv (frobeniusEquiv k 2) b) g
  have hrep : (Units.coeHom _).comp (coefficientFrobenius (A.factor a).action b).action =
      Representation.semilinearConjugate (frobeniusEquiv k 2)
        ((A.factor a).restrict (MonoidHom.id _)).ρ
        (basisCoefficientEquiv (frobeniusEquiv k 2) b) := by
    apply MonoidHom.ext
    intro x
    apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := (basisCoefficientEquiv (frobeniusEquiv k 2) b).surjective v
    change ((coefficientFrobenius (A.factor a).action b).action x).val
        (basisCoefficientEquiv (frobeniusEquiv k 2) b w) = _
    rw [coefficientFrobenius_apply]
    change (basisCoefficientEquiv (frobeniusEquiv k 2) b) (((A.factor a).action.action x).val w) =
      (basisCoefficientEquiv (frobeniusEquiv k 2) b) (((A.factor a).action.action x).val
        ((basisCoefficientEquiv (frobeniusEquiv k 2) b).symm
          (basisCoefficientEquiv (frobeniusEquiv k 2) b w)))
    exact congrArg (fun z => (basisCoefficientEquiv (frobeniusEquiv k 2) b)
      (((A.factor a).action.action x).val z))
      ((basisCoefficientEquiv (frobeniusEquiv k 2) b).symm_apply_apply w).symm
  rw [hrep] at he
  exact he.symm.trans ht

omit [CharP k 2] in
theorem basicCharacter_graph (S : D4Geometry K) (D : PinnedTriality S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding) (a : BasicWeight)
    (g : K.Point) : basicCharacter A.factor (diagramAction a) g =
      basicCharacter A.factor a (D.iso.hom.onPoints g) :=
  (congrFun (Representation.char_iso (leftGraphPullbackEquiv S D A a)) g).symm

private theorem prod_periodic_shift {M : Type*} [CommMonoid M]
    (f : ℕ → M) (n : ℕ) (hf : Function.Periodic f n) (r : ℕ) :
    (∏ i ∈ Finset.range n, f (i+r)) = ∏ i ∈ Finset.range n, f i := by
  induction r with
  | zero => simp
  | succ r ih =>
    cases n with
    | zero => simp
    | succ n =>
      calc
        (∏ i ∈ Finset.range (n+1), f (i+(r+1))) =
            (∏ i ∈ Finset.range n, f (i+(r+1))) * f r := by
              rw [Finset.prod_range_succ]
              congr 1
              simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf r
        _ = ∏ i ∈ Finset.range (n+1), f (i+r) := by
          rw [Finset.prod_range_succ']
          simp only [Nat.add_zero, Nat.add_comm, Nat.add_left_comm, mul_comm]
        _ = _ := ih

omit [IsAlgClosed k] [CharP k 2] in
theorem character_tensorPrefix {G : Type v} [Group G]
    (V : ℕ → FDRep k G) (n : ℕ) (g : G) :
    Representation.character (tensorPrefix V n).ρ g =
      ∏ i ∈ Finset.range n, Representation.character (V i).ρ g := by
  induction n with
  | zero =>
    change LinearMap.trace k k LinearMap.id = _
    simp
  | succ n ih =>
    change Representation.character (Representation.tprod (tensorPrefix V n).ρ (V n).ρ) g = _
    rw [Representation.char_tensor, Pi.mul_apply, ih, Finset.prod_range_succ]

omit [CharP k 2] in
theorem character_tensor (A : BasicWeight → RationalFactor K) (φ : Monoid.End K.Point)
    {G : Type v} [Group G] (ι : G →* K.Point) (w : ℕ → BasicWeight) (n : ℕ) (g : G) :
    Representation.character (tensor A φ ι w n).ρ g =
      ∏ i ∈ Finset.range n, basicCharacter A (w i) ((φ^i) (ι g)) := by
  rw [tensor, character_tensorPrefix]
  rfl

omit [IsAlgClosed k] [CharP k 2] in
private theorem character_pow (χ : BasicWeight → K.Point → k)
    (φ : Monoid.End K.Point) (hφ : ∀ a g, χ a (φ g) = χ a g ^ 2)
    (a : BasicWeight) (g : K.Point) (r : ℕ) : χ a ((φ^r) g) = χ a g ^ (2^r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ']
    change χ a (φ ((φ^r) g)) = _
    rw [hφ, ih, ← pow_mul, Nat.pow_succ]

omit [CharP k 2] in
/-- Cyclically shift the actual tensor factors; exponent overflow uses the
inverse graph map, so the weights wrap by the forward diagram action. -/
theorem character_tensor_shift (A : BasicWeight → RationalFactor K)
    (φ : Monoid.End K.Point) (γ : K.Point ≃* K.Point)
    (hcomm : ∀ x, φ (γ x) = γ (φ x))
    (hφ : ∀ a g, basicCharacter A a (φ g) = basicCharacter A a g ^ 2)
    (hγ : ∀ a g, basicCharacter A (diagramAction a) g = basicCharacter A a (γ g))
    {G : Type v} [Group G] (ι : G →* K.Point) (n : ℕ)
    (hfixed : ∀ g, (φ^n) (γ (ι g)) = ι g)
    (w : ℕ → BasicWeight) (hwrap : ∀ i, w (i+n) = diagramAction (w i))
    (r : ℕ) (g : G) :
    Representation.character (tensor A φ ι (fun i => w (i+r)) n).ρ g ^ (2^r) =
      Representation.character (tensor A φ ι w n).ρ g := by
  have hc (m : ℕ) (x : K.Point) : γ ((φ^m) x) = (φ^m) (γ x) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [pow_succ']
      change γ (φ ((φ^m) x)) = φ ((φ^m) (γ x))
      rw [←hcomm, ih]
  let f : ℕ → k := fun i => basicCharacter A (w i) ((φ^i) (ι g))
  have hf : Function.Periodic f n := by
    intro i
    dsimp only [f]
    rw [hwrap, hγ, pow_add]
    change basicCharacter A (w i) (γ ((φ^i) ((φ^n) (ι g)))) = _
    rw [hc, hc, hfixed]
  rw [character_tensor, character_tensor, ← Finset.prod_pow]
  calc
    (∏ i ∈ Finset.range n, basicCharacter A (w (i+r)) ((φ^i) (ι g)) ^ (2^r)) =
        ∏ i ∈ Finset.range n, f (i+r) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [←character_pow (basicCharacter A) φ hφ]
      dsimp only [f]
      rw [Nat.add_comm i r, pow_add]
      rfl
    _ = _ := prod_periodic_shift f n hf r

/-- Re-extending a shifted block gives the same shifted wrapped sequence. -/
theorem extendWeights_shift {n : ℕ} (hn : 0 < n) (a : Fin n → BasicWeight) (r : ℕ) :
    extendWeights hn (shiftWeights hn a r) = fun i => extendWeights hn a (i+r) := by
  apply eq_of_initial_of_wrap hn (extendWeights_wrap hn _)
  · intro i
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      extendWeights_wrap hn a (i+r)
  · intro i hi
    exact extendWeights_initial hn (shiftWeights hn a r) ⟨i,hi⟩

/-- Exact Frobenius periods follow from tensor trace shift and finite parameter
separation. No coefficient-twist realization is needed for this conclusion. -/
theorem character_period_of_tensor_classification
    {G : Type v} [Group G] {n : ℕ} (hn : 0 < n)
    (R : (Fin n → BasicWeight) → FDRep k G)
    (hirr : ∀ a, Representation.IsIrreducible (R a).ρ)
    (hunique : ∀ a b, Nonempty (Representation.Equiv (R a).ρ (R b).ρ) → a=b)
    (htrace : ∀ a r g, Representation.character (R (shiftWeights hn a r)).ρ g ^ (2^r) =
      Representation.character (R a).ρ g)
    (a : Fin n → BasicWeight) (r : ℕ) :
    (∀ g, Representation.character (R a).ρ g ^ (2^r) =
      Representation.character (R a).ρ g) ↔ Function.Periodic (extendWeights hn a) r := by
  rw [←shiftWeights_eq_iff hn a r]
  constructor
  · intro hfixed
    have hchar : Representation.character (R (shiftWeights hn a r)).ρ =
        Representation.character (R a).ρ := by
      funext g
      apply (iterateFrobeniusEquiv k 2 r).injective
      change Representation.character (R (shiftWeights hn a r)).ρ g ^ (2^r) =
        Representation.character (R a).ρ g ^ (2^r)
      rw [htrace, hfixed]
    let := hirr (shiftWeights hn a r)
    let := hirr a
    exact hunique _ _ ((Representation.character_eq_iff_equiv_of_irreducible _ _).mp hchar)
  · intro hshift g
    have hh := htrace a r g
    rwa [hshift] at hh


/-- Literal tensor-character transport with both basic-factor identities proved. -/
theorem left_tensor_character_shift (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (D : PinnedTriality S) (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding)
    (hcomm : ∀ x, F.morphism.onPoints (D.iso.toMulEquiv x) =
      D.iso.toMulEquiv (F.morphism.onPoints x))
    {G : Type v} [Group G] (ι : G →* K.Point) (n : ℕ)
    (hfixed : ∀ g, (pointEnd F.morphism ^ n) (D.iso.toMulEquiv (ι g)) = ι g)
    (w : ℕ → BasicWeight) (hwrap : ∀ i, w (i+n) = diagramAction (w i))
    (r : ℕ) (g : G) :
    Representation.character (tensor A.factor F.morphism.onPoints ι (fun i => w (i+r)) n).ρ g ^
      (2^r) = Representation.character (tensor A.factor F.morphism.onPoints ι w n).ρ g :=
  character_tensor_shift A.factor F.morphism.onPoints D.iso.toMulEquiv hcomm
    (basicCharacter_frobenius S F A) (basicCharacter_graph S D A)
    ι n hfixed w hwrap r g

/-- The source character-period consumer of finite irreducibility and separation.
The coefficient and graph-twist calculations are discharged on the actual tensor. -/
theorem left_tensor_character_period (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (D : PinnedTriality S) (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding)
    (hcomm : ∀ x, F.morphism.onPoints (D.iso.toMulEquiv x) =
      D.iso.toMulEquiv (F.morphism.onPoints x))
    {G : Type v} [Group G] (ι : G →* K.Point) (n : ℕ) (hn : 0<n)
    (hfixed : ∀ g, (pointEnd F.morphism ^ n) (D.iso.toMulEquiv (ι g)) = ι g)
    (hirr : ∀ a : Fin n → BasicWeight,
      Representation.IsIrreducible (tensor A.factor F.morphism.onPoints ι (extendWeights hn a) n).ρ)
    (hunique : ∀ a b : Fin n → BasicWeight,
      Nonempty (Representation.Equiv
        (tensor A.factor F.morphism.onPoints ι (extendWeights hn a) n).ρ
        (tensor A.factor F.morphism.onPoints ι (extendWeights hn b) n).ρ) → a=b)
    (a : Fin n → BasicWeight) (r : ℕ) :
    (∀ g, Representation.character (tensor A.factor F.morphism.onPoints ι (extendWeights hn a) n).ρ g ^
      (2^r) = Representation.character (tensor A.factor F.morphism.onPoints ι (extendWeights hn a) n).ρ g) ↔
        Function.Periodic (extendWeights hn a) r := by
  apply character_period_of_tensor_classification hn
    (fun a => tensor A.factor F.morphism.onPoints ι (extendWeights hn a) n) hirr hunique
  intro b s g
  rw [extendWeights_shift]
  exact left_tensor_character_shift S F D A hcomm ι n hfixed
    (extendWeights hn b) (extendWeights_wrap hn b) s g

end Triality.RestrictedWeights.SteinbergTensors
