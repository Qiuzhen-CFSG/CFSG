module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.HighestWeights
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.CoefficientFrobenius.Transport
public import Theory.AlgebraicGroup.Representations.RationalBasis

/-!
# Coefficient Frobenius and ordinary Frobenius on rational D4 factors

In any finite basis, output-only semilinear conjugation squares the matrix
entries. The coordinate-squaring map on GL is regular, and semilinear pullback
of invariant subspaces proves irreducibility. The semilinear image of a highest
vector has squared character, hence doubled integral weight. Ordinary geometric
Frobenius has the same highest weight. The opposite-Borel big-cell uniqueness
theorem then supplies an actual linear intertwiner and a bundled point-action
equivalence for every basic factor.

The reused coefficient-transport action is specialized to the identity on the
source group. Thus no inverse Frobenius on the algebraic group, nor rationality
of such an inverse, enters this construction.

Source: GLS3, Definition 2.8.3 and Remarks 2.8.4 and 2.8.8,
`refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.CoefficientTransport
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- Output-only coefficient Frobenius in a specified finite basis. -/
def coefficientFrobenius {V : Type v} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : RationalRepresentation K V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V) : RationalRepresentation K V :=
  twistAction (frobeniusEquiv k 2) (MulEquiv.refl _) ρ
    (basisCoefficientEquiv (frobeniusEquiv k 2) b)

/-- The coefficient conjugation is semilinearly intertwined with the original action. -/
theorem coefficientFrobenius_apply {V : Type v} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : RationalRepresentation K V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V) (g : Variety.Point K) (v : V) :
    ((coefficientFrobenius ρ b).action g).val
        (basisCoefficientEquiv (frobeniusEquiv k 2) b v) =
      basisCoefficientEquiv (frobeniusEquiv k 2) b ((ρ.action g).val v) :=
  twistAction_apply _ _ _ _ _ _

/-- The entries in the chosen basis are literally squared. -/
theorem coefficientFrobenius_matrix {V : Type v} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : RationalRepresentation K V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (g : Variety.Point K) (i j : Fin (Module.finrank k V)) :
    b.repr (((coefficientFrobenius ρ b).action g).val (b j)) i =
      (b.repr ((ρ.action g).val (b j)) i) ^ 2 := by
  rw [← basisCoefficientEquiv_basis (frobeniusEquiv k 2) b j,
    coefficientFrobenius_apply, basisCoefficientEquiv_coord,
    basisCoefficientEquiv_basis]
  rfl

private def glSquaring (n : ℕ) :
    Theory.AlgebraicGroup.Morphism (glVariety n : Variety k) (glVariety n) where
  toVariety :=
    { toFun := (glCoefficientAction (frobeniusEquiv k 2) n).equiv
      regular := by
        intro i
        refine ⟨MvPolynomial.X i ^ 2, fun g => ?_⟩
        rw [(glCoefficientAction (frobeniusEquiv k 2) n).coordinate]
        change (g.val i) ^ 2 = MvPolynomial.eval₂ (RingHom.id k) g.val (MvPolynomial.X i ^ 2)
        rw [MvPolynomial.eval₂_X_pow] }
  map_one := map_one _
  map_mul := map_mul _

/-- Squaring output coordinates is regular in characteristic two. -/
theorem coefficientFrobenius_rational {V : Type v} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : RationalRepresentation K V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (hρ : IsRationalRepresentation ρ) :
    IsRationalRepresentation (coefficientFrobenius ρ b) := by
  obtain ⟨f, hf⟩ := hρ.exists_morphism_in_basis b
  refine ⟨b, (glSquaring _).comp f, ?_⟩
  intro g
  change glPointEquivOf k V b
    ((glCoefficientAction (frobeniusEquiv k 2) _).equiv (f.onPoints g)) = _
  rw [glPointEquivOf_coefficient, hf]
  apply Units.ext
  apply LinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := (basisCoefficientEquiv (frobeniusEquiv k 2) b).surjective v
  change basisCoefficientEquiv (frobeniusEquiv k 2) b
    ((ρ.action g).val ((basisCoefficientEquiv (frobeniusEquiv k 2) b).symm
      (basisCoefficientEquiv (frobeniusEquiv k 2) b w))) = _
  rw [LinearEquiv.symm_apply_apply, coefficientFrobenius_apply]

/-- Semilinear conjugation transports invariant subspaces. -/
theorem coefficientFrobenius_irreducible {V : Type v} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : RationalRepresentation K V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (hρ : IsIrreducibleRepresentation ρ) :
    IsIrreducibleRepresentation (coefficientFrobenius ρ b) :=
  ⟨coefficientFrobenius_rational ρ b hρ.1,
    twistAction_irreducible _ _ _ _ hρ.2⟩

omit [IsAlgClosed k] [CharP k 2] in
private theorem character_square (T : ClosedSubgroup K) (χ : TorusWeight T)
    (t : Variety.Point T.carrierVariety) :
    (χ ^ 2).pointCharacter t = χ.pointCharacter t ^ 2 := by
  rw [pow_two]
  change (dPointEquiv 1 (χ.onPoints t * χ.onPoints t) 0 : k) = _
  rw [dPointEquiv_mul]
  exact (pow_two _).symm

/-- The semilinear image of a highest vector has doubled highest weight. -/
theorem coefficientFrobenius_hasHighWeight {V : Type v} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : RationalRepresentation K V)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (B T : ClosedSubgroup K) (v : V) (χ : TorusWeight T)
    (hv : HasHighWeight ρ B T v χ) :
    HasHighWeight (coefficientFrobenius ρ b) B T
      (basisCoefficientEquiv (frobeniusEquiv k 2) b v) (χ ^ 2) := by
  let e := basisCoefficientEquiv (frobeniusEquiv k 2) b
  have hn : e v ≠ 0 := fun h => hv.1.1 (e.injective (h.trans e.map_zero.symm))
  refine ⟨⟨hn, ?_⟩, hn, ?_⟩
  · intro g hg
    obtain ⟨c, hc⟩ := hv.1.2 g hg
    refine ⟨c ^ 2, ?_⟩
    rw [coefficientFrobenius_apply, hc, map_smulₛₗ]
    rfl
  · intro t
    rw [coefficientFrobenius_apply, hv.2.2, map_smulₛₗ, character_square]
    rfl

omit [IsAlgClosed k] [CharP k 2] in
/-- Squaring characters doubles their actual integral coordinates. -/
theorem weightEmbedding_double (S : D4Geometry K) (x : Weight) :
    S.weightEmbedding ((2 : ℕ) • x) = S.weightEmbedding x ^ 2 := by
  change S.characters (Multiplicative.ofAdd ((2 : ℕ) • x)) = _
  rw [ofAdd_nsmul, map_pow]
  rfl

/-- For every basic factor the actual character is the doubled coordinate weight. -/
theorem coefficientFrobenius_basic_highest (S : D4Geometry K)
    (A : RationalBasicFamily S.borel S.torus S.weightEmbedding) (a : BasicWeight)
    (b : Module.Basis (Fin (Module.finrank k (A.factor a).Space)) k (A.factor a).Space) :
    ∃ v, HasHighWeight (coefficientFrobenius (A.factor a).action b) S.borel S.torus v
      (S.weightEmbedding ((2 : ℕ) • coefficient a)) := by
  obtain ⟨v, hv⟩ := A.highest a
  rw [weightEmbedding_double]
  exact ⟨_, coefficientFrobenius_hasHighWeight _ b _ _ v _ hv⟩

/-- Coefficient Frobenius and ordinary geometric Frobenius have an actual
linear intertwining equivalence, by the proved highest-weight uniqueness theorem. -/
theorem coefficientFrobenius_equivalent (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.weightEmbedding) (a : BasicWeight)
    (b : Module.Basis (Fin (Module.finrank k (A.factor a).Space)) k (A.factor a).Space) :
    ∃ e : (A.factor a).Space ≃ₗ[k] (A.factor a).Space,
      Intertwines (coefficientFrobenius (A.factor a).action b)
        (pullback F.morphism (A.factor a).action) e.toLinearMap := by
  obtain ⟨v, hv⟩ := A.highest a
  exact irreducible_highWeight_equivalent_of_oppositeBorelBigCell S.bigCell S.maximalTorus
    _ _ (coefficientFrobenius_irreducible _ b (A.factor a).irreducible)
    (pullback_irreducible F.morphism F.surjective _ (A.factor a).irreducible)
    _ _ _ (coefficientFrobenius_hasHighWeight _ b _ _ v _ hv)
    (pullback_hasHighWeight_pow _ _ F.morphism 2 F.borel_stable F.torus_formula _ v _ hv)

/-- A bundled intertwiner between coefficient Frobenius and geometric Frobenius.
The coefficients are squared in `b`; the target pulls back along `F.morphism`. -/
def coefficientFrobeniusEquiv (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.weightEmbedding) (a : BasicWeight)
    (b : Module.Basis (Fin (Module.finrank k (A.factor a).Space)) k (A.factor a).Space) :
    Representation.Equiv
      ((Units.coeHom _).comp (coefficientFrobenius (A.factor a).action b).action)
      ((A.factor a).restrict F.morphism.onPoints).ρ :=
  .mk (coefficientFrobenius_equivalent S F A a b).choose
    (fun g => LinearMap.ext ((coefficientFrobenius_equivalent S F A a b).choose_spec g))

end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
