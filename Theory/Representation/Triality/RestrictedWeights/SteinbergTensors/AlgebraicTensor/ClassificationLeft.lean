module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.TensorRecursion
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.LeftWeights.Tensors
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.Weights

/-!
# Rational D4 Steinberg tensors in left highest-weight coordinates

The family is the existing `RationalBasicFamily` at `S.leftWeightEmbedding`.
Splitting off the first digit and applying the proved restricted Frobenius
step proves irreducibility of every actual tensor. Its already constructed
highest vector has coordinates `sum (2^i * coefficient(a_i))`. Binary expansion
and highest-weight uniqueness then give exhaustivity and unique parameters
at each fixed length, with actual linear and point-representation intertwiners.
Length one and zero digits are included.

The coordinates are evaluated on the actual left simple coroots through the
published adapter. The positive Borel, raw root data, regular Frobenius,
carriers and tensor actions are unchanged. This theorem concerns rational
representations; irreducibility and uniqueness after finite restriction are
separate results. Existence of the sixteen basic factors remains the input
specified by `RationalBasicFamily`, not a tensor-classification hypothesis.

Sources: GLS3, Definitions 2.8.1/2.8.3, Theorem 2.8.5 and the rational part
of Corollary 2.8.6(a), `refs/KGroup/GLS3/chapter2.tex`; Steinberg, equation
(6.1) and Theorem 13.1, `refs/KGroup/GLS3/Chapter2St2.tex`.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
open scoped TensorProduct
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
universe u v w
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

/-- Every specified tensor is rational irreducible in the left highest-weight
normalization, including lengths zero and one. The induction uses the proved
restricted root-operator theorem on its first digit. -/
theorem leftRationalTensor_irreducible [CharP k 2]
    (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding)
    (a : ℕ → BasicWeight) (n : ℕ) :
    IsIrreducibleRepresentation (rationalTensor A.factor (pointEnd F.morphism) a n) := by
  induction n generalizing a with
  | zero =>
    refine ⟨rationalTensor_rational _ _ _ _, fun U _ => ?_⟩
    change Submodule k k at U
    let : IsSimpleOrder (Submodule k k) :=
      is_simple_module_of_finrank_eq_one (Module.finrank_self k)
    exact eq_bot_or_eq_top U
  | succ n ih =>
    have ht := RestrictedStep.tensorPullback_irreducible_of_left_basic_highWeight S F
      (A.factor (a 0)).action
      (rationalTensor A.factor (pointEnd F.morphism) (fun i => a (i + 1)) n)
      (A.factor (a 0)).irreducible (ih _) (a 0) (A.highest (a 0))
    let e := tensorHeadEquiv A.factor (pointEnd F.morphism) a n
    refine ⟨rationalTensor_rational _ _ _ _,
      algebraicallyIrreducible_of_equiv _ _ e.toLinearEquiv ?_ ht.2⟩
    intro g v
    exact LinearMap.congr_fun (e.isIntertwining' g) v


/-- Extend a fixed-length binary word by zero digits. Only its first `n`
entries enter the actual tensor construction. -/
def extendWord {n : ℕ} (a : Fin n → BasicWeight) : ℕ → BasicWeight :=
  fun i => if hi : i < n then a ⟨i, hi⟩ else fun _ => false

/-- The extension retains every digit of the original fixed-length word. -/
@[simp] theorem extendWord_apply {n : ℕ} (a : Fin n → BasicWeight) (i : Fin n) :
    extendWord a i = a i := dif_pos i.isLt

/-- The highest-weight sum of a tensor depends precisely on its first `n` digits. -/
theorem tensorWeight_eq_wordWeight (a : ℕ → BasicWeight) (n : ℕ) :
    tensorWeight a n = wordWeight n (fun i => a i.val) := by
  rw [tensorWeight, Finset.sum_range, wordWeight_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  ext j
  simp [Pi.smul_apply]

/-- The tensor on an extended word has exactly its recursive binary weight. -/
@[simp] theorem tensorWeight_extendWord {n : ℕ} (a : Fin n → BasicWeight) :
    tensorWeight (extendWord a) n = wordWeight n a := by
  rw [tensorWeight_eq_wordWeight]
  simp only [extendWord_apply]

/-- Two highest vectors of one rational irreducible have equal left coordinates,
by uniqueness of the highest line in the actual opposite-Borel big cell. -/
theorem leftHighestWeight_unique (S : D4Geometry K)
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation K V) (hρ : IsIrreducibleRepresentation ρ)
    {a b : Weight}
    (ha : ∃ v, HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding a))
    (hb : ∃ v, HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding b)) : a = b := by
  obtain ⟨v, hv⟩ := ha
  obtain ⟨w, hw⟩ := hb
  obtain ⟨c, _, hwv⟩ := irreducible_highWeight_unique_line_of_oppositeBorelBigCell
    S.bigCell S.maximalTorus ρ hρ v w _ _ hv hw
  apply S.leftWeightEmbedding.injective
  apply TorusCharacter.pointCharacter_injective
  ext t
  have heq : (ρ.action (S.torus.includePoint t)).1 w =
      (S.leftWeightEmbedding a).pointCharacter t • w := by
    rw [hwv, map_smul, hv.2.2 t]
    exact smul_comm _ _ _
  exact smul_left_injective k hw.1.1 (heq.symm.trans (hw.2.2 t))

omit [IsAlgClosed k] in
/-- An actual algebraic intertwiner carries a left highest vector to one with
the same character, without requiring irreducibility. -/
theorem leftHighestWeight_of_equivalent (S : D4Geometry K)
    {V : Type v} {W : Type w} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W)
    {a : Weight}
    (ha : ∃ v, HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding a))
    (he : AreEquivalentRepresentations ρ σ) :
    ∃ v, HasHighWeight σ S.borel S.torus v (S.leftWeightEmbedding a) := by
  obtain ⟨v, hv⟩ := ha
  obtain ⟨e, he⟩ := he
  have hne : e v ≠ 0 := by simpa using hv.1.1
  refine ⟨e v, ⟨hne, ?_⟩, hne, ?_⟩
  · intro g hg
    obtain ⟨c, hc⟩ := hv.1.2 g hg
    refine ⟨c, ?_⟩
    calc
      (σ.action g).1 (e v) = e ((ρ.action g).1 v) := (he g v).symm
      _ = c • e v := by rw [hc, e.map_smul]
  · intro t
    calc
      (σ.action (S.torus.includePoint t)).1 (e v) =
          e ((ρ.action (S.torus.includePoint t)).1 v) :=
        (he (S.torus.includePoint t) v).symm
      _ = (S.leftWeightEmbedding a).pointCharacter t • e v := by
        rw [hv.2.2 t, e.map_smul]

variable [CharP k 2]

/-- The existing tensor, with its proved rational irreducibility and nonzero
highest vector, packaged for consumers requiring a `RationalFactor`. -/
def leftRationalTensorFactor (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding)
    (a : ℕ → BasicWeight) (n : ℕ) : RationalFactor K where
  Space := tensor A.factor (pointEnd F.morphism) (MonoidHom.id _) a n
  nonzero := by
    obtain ⟨v, hv⟩ := leftRationalTensor_hasHighWeight_sum S F A a n
    exact ⟨⟨v, 0, hv.1.1⟩⟩
  action := rationalTensor A.factor (pointEnd F.morphism) a n
  irreducible := leftRationalTensor_irreducible S F A a n

/-- The actual rational tensor attached to a fixed-length binary word. -/
def leftWordTensor (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding)
    (n : ℕ) (a : Fin n → BasicWeight) : RationalFactor K :=
  leftRationalTensorFactor S F A (extendWord a) n

set_option backward.isDefEq.respectTransparency false in
/-- The highest weight of the word tensor is its binary coordinate sum. -/
theorem leftWordTensor_hasHighWeight (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding)
    (n : ℕ) (a : Fin n → BasicWeight) :
    ∃ v, HasHighWeight (leftWordTensor S F A n a).action S.borel S.torus v
      (S.leftWeightEmbedding (wordWeight n a)) := by
  change ∃ v, HasHighWeight (rationalTensor A.factor (pointEnd F.morphism) (extendWord a) n)
    S.borel S.torus v (S.leftWeightEmbedding (wordWeight n a))
  simpa only [tensorWeight_extendWord] using
    leftRationalTensor_hasHighWeight_sum S F A (extendWord a) n

/-- Every rational irreducible of the specified tensor highest weight has an
actual linear intertwining equivalence to that tensor. -/
theorem leftRationalTensor_equivalent_of_highestWeight (S : D4Geometry K)
    (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding)
    (C : RationalFactor K) (a : ℕ → BasicWeight) (n : ℕ)
    (hC : ∃ v, HasHighWeight C.action S.borel S.torus v
      (S.leftWeightEmbedding (tensorWeight a n))) :
    AreEquivalentRepresentations C.action
      (rationalTensor A.factor (pointEnd F.morphism) a n) := by
  obtain ⟨v, hv⟩ := hC
  obtain ⟨w, hw⟩ := leftRationalTensor_hasHighWeight_sum S F A a n
  exact irreducible_highWeight_equivalent_of_oppositeBorelBigCell
    S.bigCell S.maximalTorus _ _ C.irreducible
    (leftRationalTensor_irreducible S F A a n) v w _ hv hw

/-- Distinct length-`n` words give inequivalent rational representations.
This is equivalence on the full algebraic point group, before finite restriction. -/
theorem leftWordTensor_equivalent_iff (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding)
    (n : ℕ) (a b : Fin n → BasicWeight) :
    AreEquivalentRepresentations (leftWordTensor S F A n a).action
      (leftWordTensor S F A n b).action ↔ a = b := by
  constructor
  · intro he
    apply wordWeight_injective n
    exact leftHighestWeight_unique S _ (leftWordTensor S F A n b).irreducible
      (leftHighestWeight_of_equivalent S _ _ (leftWordTensor_hasHighWeight S F A n a) he)
      (leftWordTensor_hasHighWeight S F A n b)
  · rintro rfl
    exact ⟨LinearEquiv.refl k _, fun _ _ => rfl⟩

/-- Every rational irreducible whose left highest-weight coordinates lie in
`[0, 2^n)` is equivalent to exactly one length-`n` binary tensor. The witness
is an actual linear intertwiner; no tensor classification is an input. -/
theorem leftRationalTensor_exhaustive (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding)
    (C : RationalFactor K) (n : ℕ) (x : Weight)
    (hx : InRestrictedRange n x)
    (hC : ∃ v, HasHighWeight C.action S.borel S.torus v (S.leftWeightEmbedding x)) :
    ∃! a : Fin n → BasicWeight,
      AreEquivalentRepresentations C.action (leftWordTensor S F A n a).action := by
  obtain ⟨a, ha⟩ := exists_wordWeight n x hx
  have he : AreEquivalentRepresentations C.action (leftWordTensor S F A n a).action := by
    apply leftRationalTensor_equivalent_of_highestWeight S F A C (extendWord a) n
    simpa only [tensorWeight_extendWord, ha] using hC
  refine ⟨a, he, ?_⟩
  intro b hb
  apply wordWeight_injective n
  have hxw := leftHighestWeight_unique S _ (leftWordTensor S F A n b).irreducible
    (leftHighestWeight_of_equivalent S _ _ hC hb)
    (leftWordTensor_hasHighWeight S F A n b)
  exact hxw.symm.trans ha.symm


/-- The bundled point-representation equivalence supplied by highest-weight
uniqueness and the proved tensor irreducibility. -/
def leftRationalTensorEquiv (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding)
    (C : RationalFactor K) (a : ℕ → BasicWeight) (n : ℕ)
    (hC : ∃ v, HasHighWeight C.action S.borel S.torus v
      (S.leftWeightEmbedding (tensorWeight a n))) :
    Representation.Equiv (C.restrict (MonoidHom.id _)).ρ
      (tensor A.factor (pointEnd F.morphism) (MonoidHom.id _) a n).ρ :=
  .mk (leftRationalTensor_equivalent_of_highestWeight S F A C a n hC).choose
    (fun g => LinearMap.ext
      ((leftRationalTensor_equivalent_of_highestWeight S F A C a n hC).choose_spec g))

/-- At length one, the word tensor is actually equivalent to its basic factor.
In particular, the field-two boundary is included. -/
def leftWordTensorOneEquiv (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding)
    (a : Fin 1 → BasicWeight) :
    Representation.Equiv ((leftWordTensor S F A 1 a).restrict (MonoidHom.id _)).ρ
      ((A.factor (a 0)).restrict (MonoidHom.id _)).ρ := by
  have e := tensorOneEquiv A.factor (pointEnd F.morphism) (MonoidHom.id _) (extendWord a)
  exact e

/-- Fixed-length rational exhaustivity with a bundled `Representation.Equiv`
to the literal tensor action from `Construction`. -/
theorem leftRationalTensor_exhaustive_point (S : D4Geometry K) (F : OrdinaryFrobenius S)
    (A : RationalBasicFamily S.borel S.torus S.leftWeightEmbedding)
    (C : RationalFactor K) (n : ℕ) (x : Weight)
    (hx : InRestrictedRange n x)
    (hC : ∃ v, HasHighWeight C.action S.borel S.torus v (S.leftWeightEmbedding x)) :
    ∃! a : Fin n → BasicWeight, Nonempty (Representation.Equiv
      (C.restrict (MonoidHom.id _)).ρ
      (tensor A.factor (pointEnd F.morphism) (MonoidHom.id _) (extendWord a) n).ρ) := by
  obtain ⟨a, ha, hu⟩ := leftRationalTensor_exhaustive S F A C n x hx hC
  refine ⟨a, ?_, ?_⟩
  · obtain ⟨e, he⟩ := ha
    exact ⟨.mk e (fun g => LinearMap.ext (he g))⟩
  · rintro b ⟨e⟩
    apply hu b
    exact ⟨e.toLinearEquiv, fun g v => LinearMap.congr_fun (e.isIntertwining' g) v⟩


end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
