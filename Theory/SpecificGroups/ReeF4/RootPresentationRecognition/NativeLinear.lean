module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.NativeRankOne
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.LinearCover.RankOne
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Relations.LinearRigidity.OppositeWords

/-!
# Signed linear and Gauss relations in the full Ree group

The native additive charts cover both signed type VI root intersections.
The paired Weyl word satisfies the root braid identity; its ratio with the
parameter-one reflection is the product of the actual end-node coroots.
This gives the linear Gauss equation with the same full two-dimensional
Cartan used in the Suzuki branch, for every m including zero.

Source: GLS3, Table 2.4 type VI and §§2.3--2.5; Steinberg §11,
`refs/KGroup/GLS3/Chapter2St1.tex`. The split end-node commutation argument
adapts `LocalIndices/LinearCover/RankOne.lean`.
-/



@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition
open Subgroup LargeLocalSeeds Parabolics
open LocalBlockInput.PairRigidity LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open LocalBlockInput.PairRigidity.LocalIndices
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open CentralCovers.OddPrimary.Order
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
variable {m : ℕ}

/-- The actual signed linear chart in the full Ree group. -/
def linear (m : ℕ) (p : Bool) (t : CoefficientField m) : Model m :=
  (canonicalLocalBlockInput m).modelEquiv (linearElement _ p t)

@[simp] theorem linear_split (p : Bool) (t : CoefficientField m) :
    toSplitGroup m (linear m p t) = linearWord m p t := by
  rw [linear, toSplitGroup_apply, LocalBlockInput.modelEquiv_coe, linearElement_word]

theorem linear_mem (p : Bool) (t : CoefficientField m) :
    linear m p t ∈ rootBlock m .linear p := by
  change toSplitGroup m (linear m p t) ∈ splitSimpleBlock m .linear p
  rw [linear_split, ← linearElement_word (canonicalLocalBlockInput m)]
  exact linearElement_mem _ _ _

theorem linear_injective (p : Bool) : Function.Injective (linear m p) :=
  (canonicalLocalBlockInput m).modelEquiv.injective.comp (linearElement_injective _ p)

theorem linear_cover (p : Bool) (x : Model m) (hx : x ∈ rootBlock m .linear p) :
    ∃ t, linear m p t = x := by
  let d := canonicalLocalBlockInput m
  have hx' : d.modelEquiv.symm x ∈ simpleBlock d .linear p := by
    change (d.modelEquiv.symm x).val ∈ splitSimpleBlock m .linear p
    rw [modelEquiv_symm_coe]
    simpa only [rootBlock, mem_comap, toSplitGroup_apply] using hx
  obtain ⟨t, ht⟩ := linearElement_surjective d p hx'
  exact ⟨t, (congrArg d.modelEquiv ht).trans (d.modelEquiv.apply_symm_apply x)⟩

@[simp] theorem linear_zero (p : Bool) : linear m p 0 = 1 := by
  rw [linear, LocalIndices.linearElement_zero, map_one]

theorem linear_mul (p : Bool) (a b : CoefficientField m) :
    linear m p a * linear m p b = linear m p (a+b) := by
  exact (map_mul (canonicalLocalBlockInput m).modelEquiv _ _).symm.trans
    (congrArg (canonicalLocalBlockInput m).modelEquiv (linearElement_add _ p a b).symm)

@[simp] theorem linear_inv (p : Bool) (a : CoefficientField m) :
    (linear m p a)⁻¹ = linear m p a := by
  apply inv_eq_of_mul_eq_one_right
  rw [linear_mul, CharTwo.add_self_eq_zero, linear_zero]

/-- The entire Cartan acts with the prescribed signed first character. -/
theorem torus_linear (a : TorusParameter m) (p : Bool) (t : CoefficientField m) :
    torus m a * linear m p t * (torus m a)⁻¹ =
      linear m p ((signedScale a.1 p : CoefficientField m)*t) := by
  apply toSplitGroup_injective m
  rw [map_mul, map_mul, map_inv, linear_split, linear_split]
  apply Subtype.ext
  have ht : (toSplitGroup m (torus m a)).val =
      (BlockParameters.torusMatrix (blockTorus a.1 a.2))⁻¹ :=
    ConverseParabolics.FullLeviRepresentation.torusElement_matrix a.1 a.2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, ht]
  exact blockTorus_linearWord a.1 a.2 p t

/-- Nonzero linear Weyl words retain their literal three root factors. -/
def linearWeyl (m : ℕ) (a : (CoefficientField m)ˣ) : Model m :=
  (canonicalLocalBlockInput m).modelEquiv (linearPanelWeyl _ a)

theorem linearWeyl_word (a : (CoefficientField m)ˣ) :
    linearWeyl m a = linear m true a * linear m false (a⁻¹ : (CoefficientField m)ˣ) *
      linear m true a := by
  simp only [linearWeyl, linearPanelWeyl, map_mul, linear]

@[simp] theorem linearWeyl_one : linearWeyl m 1 = reflection m .linear := by
  apply toSplitGroup_injective m
  rw [linearWeyl, toSplitGroup_apply, LocalBlockInput.modelEquiv_coe, linearPanelWeyl_split,
    reflection_split]
  simp only [Units.val_one, map_one, Binary.FixedGeometry.sideWord,
    Binary.FixedGeometry.simpleWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]

/-- The two braid words agree without a rank-one simplicity hypothesis. -/
theorem linearWeyl_braid (a : (CoefficientField m)ˣ) :
    linearWeyl m a = linear m false (a⁻¹ : (CoefficientField m)ˣ) * linear m true a *
      linear m false (a⁻¹ : (CoefficientField m)ˣ) := by
  have he := congrArg (canonicalLocalBlockInput m).modelEquiv
    (linearElement_braid (canonicalLocalBlockInput m) (a : CoefficientField m) a.ne_zero)
  simpa only [map_mul, ← Units.val_inv_eq_inv_val, linearWeyl, linearPanelWeyl, linear] using he

theorem reflection_linear (p : Bool) (a : CoefficientField m) :
    reflection m .linear * linear m p a * reflection m .linear = linear m (!p) a := by
  rw [← linearWeyl_one]
  have hi := LocalIndices.linearPanelWeyl_inv (canonicalLocalBlockInput m) 1
  cases p
  · have he := congrArg (fun z => (canonicalLocalBlockInput m).modelEquiv z)
      (linearPanelWeyl_conj_negative (canonicalLocalBlockInput m) a)
    simpa only [map_mul, hi, linearWeyl, linear, Bool.not_false, Bool.not_true] using he
  · have he := congrArg (fun z => (canonicalLocalBlockInput m).modelEquiv z)
      (linearPanelWeyl_conj_positive (canonicalLocalBlockInput m) a)
    simpa only [map_mul, hi, linearWeyl, linear, Bool.not_false, Bool.not_true] using he

private theorem end_commute (p q : Bool) (t u : CoefficientField m) :
    Commute (rootGeneratorInGroup m (signedRoot p (typeF4SimpleRootIndex 0)) t)
      (rootGeneratorInGroup m (signedRoot q (typeF4SimpleRootIndex 3)) u) := by
  have hne : typeF4RootPairing_baseEquiv 0 ≠ typeF4RootPairing_baseEquiv 3 := by
    intro h
    have := typeF4RootPairing_baseEquiv.injective h
    contradiction
  have hc : typeF4RootPairing_base.cartanMatrix
      (typeF4RootPairing_baseEquiv 3) (typeF4RootPairing_baseEquiv 0) = 0 := by
    rw [typeF4RootPairing_base_cartan_apply]
    norm_num [typeF4CartanMatrix, Fin.ext_iff]
  apply Subtype.ext
  cases p <;> cases q
  all_goals
    simp only [signedRoot, Bool.false_eq_true, ↓reduceIte]
    change F4Chevalley.rootCurve _ t * F4Chevalley.rootCurve _ u =
      F4Chevalley.rootCurve _ u * F4Chevalley.rootCurve _ t
    simp only [F4Chevalley.rootCurve, F4Chevalley.integralOperators,
      ← typeF4RootPairing_baseEquiv_val, rootCurveUnit_simple, rootCurveUnit_neg_simple]
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_negative_negative_of_cartan_eq_zero _ _ hne hc t u).eq
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_positive_negative _ _ hne.symm u t).eq.symm
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_positive_negative _ _ hne t u).eq
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_positive_positive_of_cartan_eq_zero _ _ hne hc t u).eq

private theorem end_weyl_commute (a b : CoefficientField m) :
    Commute (weylWord m (typeF4SimpleRootIndex 0) a)
      (weylWord m (typeF4SimpleRootIndex 3) b) := by
  have h (p : Bool) (t : CoefficientField m) :
      Commute (rootGeneratorInGroup m (signedRoot p (typeF4SimpleRootIndex 0)) t)
        (weylWord m (typeF4SimpleRootIndex 3) b) := by
    simpa only [weylWord, signedRoot, Bool.false_eq_true, ↓reduceIte] using
      ((end_commute p true t b).mul_right (end_commute p false t (-b⁻¹))).mul_right
        (end_commute p true t b)
  exact ((h true a).mul_left (h false (-a⁻¹))).mul_left (h true a)

/-- The linear Gauss torus is the actual product of its two end coroots. -/
theorem linearWeyl_ratio_split (a : (CoefficientField m)ˣ) :
    toSplitGroup m (linearWeyl m a * reflection m .linear) =
      torusWord m (typeF4SimpleRootIndex 0) a *
        torusWord m (typeF4SimpleRootIndex 3)
          (Units.map (rootFieldEnd m (typeF4SimpleRootIndex 0)).toMonoidHom a) := by
  rw [← linearWeyl_one, map_mul]
  simp only [linearWeyl, toSplitGroup_apply, LocalBlockInput.modelEquiv_coe,
    linearPanelWeyl_split, Units.val_one, map_one, torusWord, CharTwo.neg_eq]
  exact (end_weyl_commute 1 _).symm.mul_mul_mul_comm _ _

def linearTorus (a : (CoefficientField m)ˣ) : fixedTorus m :=
  ⟨linearWeyl m a * reflection m .linear, by
    change toSplitGroup m _ ∈ splitTorus m
    rw [linearWeyl_ratio_split]
    exact mul_mem (subset_closure ⟨_, _, rfl⟩) (subset_closure ⟨_, _, rfl⟩)⟩

/-- Canonical parameters in the same full Cartan as the Suzuki relation. -/
def linearTau (a : (CoefficientField m)ˣ) : TorusParameter m :=
  (fixedTorusEquiv m).symm (linearTorus a)

@[simp] theorem torus_linearTau (a : (CoefficientField m)ˣ) :
    torus m (linearTau a) = linearWeyl m a * reflection m .linear := by
  exact congrArg Subtype.val ((fixedTorusEquiv m).apply_symm_apply (linearTorus a))

/-- The literal linear Gauss relation, with the same full-torus map. -/
theorem linear_gauss (a : (CoefficientField m)ˣ) :
    reflection m .linear * linear m false a =
      linear m false (a⁻¹ : (CoefficientField m)ˣ) * torus m (linearTau a) *
        linear m true (a⁻¹ : (CoefficientField m)ˣ) := by
  have hmove (t : CoefficientField m) :
      reflection m .linear * linear m true t = linear m false t * reflection m .linear := by
    have h := congrArg (· * reflection m .linear) (reflection_linear true t)
    simpa only [Bool.not_true, mul_assoc, reflection_sq, mul_one] using h
  have hs (p : Bool) (t : CoefficientField m) : linear m p t * linear m p t = 1 := by
    rw [linear_mul, CharTwo.add_self_eq_zero, linear_zero]
  have hleft (t : CoefficientField m) :
      reflection m .linear * linear m false t = linear m true t * reflection m .linear := by
    have he := congrArg (· * reflection m .linear) (reflection_linear false t)
    simpa only [Bool.not_false, mul_assoc, reflection_sq, mul_one] using he
  rw [hleft]
  symm
  calc
    _ = linear m false (a⁻¹ : (CoefficientField m)ˣ) * linearWeyl m a *
        (reflection m .linear * linear m true (a⁻¹ : (CoefficientField m)ˣ)) := by
      rw [torus_linearTau]
      group
    _ = linear m false (a⁻¹ : (CoefficientField m)ˣ) *
        (linear m false (a⁻¹ : (CoefficientField m)ˣ) * linear m true a *
          linear m false (a⁻¹ : (CoefficientField m)ˣ)) *
        (linear m false (a⁻¹ : (CoefficientField m)ˣ) * reflection m .linear) := by
      rw [hmove, linearWeyl_braid]
    _ = _ := by
      have hc (p : Bool) (t : CoefficientField m) (x : Model m) :
          linear m p t * (linear m p t * x) = x := by
        rw [← mul_assoc, hs, one_mul]
      simp only [mul_assoc, hc]

/-- The full Cartan normalizes the negative type VI root, with no field-size restriction. -/
theorem torus_normalizes_linear_negative (m : ℕ) :
    fixedTorus m ≤ normalizer (rootBlock m .linear false) := by
  rw [le_normalizer_iff]
  intro t ht x hx
  rw [← torus_range] at ht
  obtain ⟨a,rfl⟩ := ht
  obtain ⟨u,rfl⟩ := linear_cover false x hx
  rw [torus_linear]
  exact linear_mem _ _

/-- Linear Gauss in the form consumed by the abstract two-cell collector. -/
theorem linear_gauss_conjugate (a : (CoefficientField m)ˣ) :
    reflection m .linear * linear m false a * reflection m .linear =
      linear m false (a⁻¹ : (CoefficientField m)ˣ) * torus m (linearTau a) *
        reflection m .linear * linear m false (a⁻¹ : (CoefficientField m)ˣ) := by
  rw [linear_gauss]
  have he := reflection_linear (m := m) false (↑(a⁻¹) : CoefficientField m)
  simp only [Bool.not_false] at he
  rw [← he]
  simp only [mul_assoc,reflection_sq,mul_one]

/-- Application of the local relations to every word in the native linear
root, full Cartan and literal reflection, including the binary group. -/
theorem linear_rankOne_normalForm (g : Model m)
    (hg : g ∈ rootBlock m .linear false ⊔ fixedTorus m ⊔ zpowers (reflection m .linear)) :
    RankOne.NormalForm (rootBlock m .linear false) (fixedTorus m) (reflection m .linear) g := by
  apply RankOne.normalForm_of_mem _ _ _ (torus_normalizes_linear_negative m)
    (SmallCompletion.reflection_mem_normalizer_fixedTorus m .linear)
    (reflection_sq m .linear) ?_ hg
  intro x hx hx1
  obtain ⟨t,rfl⟩ := linear_cover false x hx
  have ht : t ≠ 0 := by intro ht; exact hx1 (by rw [ht,linear_zero])
  let a : (CoefficientField m)ˣ := Units.mk0 t ht
  refine ⟨linear m false (a⁻¹ : (CoefficientField m)ˣ),linear_mem _ _,
    torus m (linearTau a),?_,linear m false (a⁻¹ : (CoefficientField m)ˣ),linear_mem _ _,
    linear_gauss_conjugate a⟩
  rw [← torus_range]
  exact ⟨_,rfl⟩

end ReeF4.RootPresentationRecognition
