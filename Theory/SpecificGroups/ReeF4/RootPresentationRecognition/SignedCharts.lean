module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SignedGeometry
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.NativeLinear
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularPresentation

/-!
# Signed Ree charts with the literal Weyl and Gauss equations

Conjugating the checked positive charts by the longest native Weyl word
constructs the eight negative charts in the actual full Model m. The finite
split-root table proves that all sixteen Weyl words preserve the field
parameters, including both coordinates of every nonabelian Suzuki root.
Local multiplication and injectivity follow by conjugation. The two simple
carriers are identified with the existing signed fixed-block intersections,
so the established linear and Suzuki Gauss identities use exactly the same
full Cartan and reflection lifts. Every m, including zero, is retained.

Source: GLS3 2.3.6--8 and Table 2.4, `refs/KGroup/GLS3/chapter2.tex`;
Steinberg, Lectures on Chevalley Groups, section 11, Lemmas 62--64.
This is the signed-root part of the presentation; global Bruhat collection
and whole-group evaluation faithfulness remain separate obligations.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.SignedCharts
open SignedGeometry WeylPresentation
open Parabolics.RadicalCoordinates FixedCoordinates
open LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
open Subgroup

def signConj (m : ℕ) (p : Bool) : MulAut (Model m) :=
  if p then 1 else MulAut.conj (NormalizerPresentation.weyl m opposition)

def pair (m : ℕ) (r : Index) (a : CoefficientField m) : Model m :=
  signConj m r.1 (PositiveTables.pair m r.2 a)

def quartet (m : ℕ) (r : Index) (a b : CoefficientField m) : Model m :=
  signConj m r.1 (PositiveTables.quartet m r.2 a b)

@[simp] theorem pair_positive (m : ℕ) (i : Fin 4) (a : CoefficientField m) :
    pair m (true,i) a = PositiveTables.pair m i a := rfl
@[simp] theorem quartet_positive (m : ℕ) (i : Fin 4) (a b : CoefficientField m) :
    quartet m (true,i) a b = PositiveTables.quartet m i a b := rfl

@[simp] theorem pair_zero (m : ℕ) (r : Index) : pair m r 0 = 1 := by
  simp only [pair, PositiveTables.pair_zero, coe_one, map_one]
@[simp] theorem quartet_zero (m : ℕ) (r : Index) : quartet m r 0 0 = 1 := by
  simp only [quartet, PositiveTables.quartet_zero, coe_one, map_one]

theorem pair_mul (m : ℕ) (r : Index) (a b : CoefficientField m) :
    pair m r a * pair m r b = pair m r (a+b) := by
  unfold pair
  rw [← map_mul, ← coe_mul, PositiveTables.pair_mul]

theorem quartet_mul (m : ℕ) (r : Index) (a b c d : CoefficientField m) :
    quartet m r a b * quartet m r c d = quartet m r (a+c) (b+d+titsEnd m a*c) := by
  unfold quartet
  rw [← map_mul, ← coe_mul, PositiveTables.quartet_mul]

theorem pair_injective (m : ℕ) (r : Index) : Function.Injective (pair m r) := by
  intro a b he
  apply PositiveTables.root_injective (.inl r.2)
  exact Subtype.ext ((signConj m r.1).injective he)

theorem quartet_injective (m : ℕ) (r : Index) :
    Function.Injective (fun a : CoefficientField m × CoefficientField m => quartet m r a.1 a.2) := by
  intro a b he
  apply PositiveTables.root_injective (.inr r.2)
  exact Subtype.ext ((signConj m r.1).injective he)

private theorem pairWord_conj (m : ℕ) (w : Weyl) (r : Index)
    (t : Fin 2 → CoefficientField m) :
    (MulAut.conj (toSplitGroup m (NormalizerPresentation.weyl m w)))
      (pairWord m (root false r) t) = pairWord m (root false (action false w r)) t := by
  simp only [pairWord, map_mul, MulAut.conj_apply, split_conjugation]

private theorem quartetWord_conj (m : ℕ) (w : Weyl) (r : Index)
    (t : Fin 4 → CoefficientField m) :
    (MulAut.conj (toSplitGroup m (NormalizerPresentation.weyl m w)))
      (quartetWord m (root true r) t) = quartetWord m (root true (action true w r)) t := by
  simp only [quartetWord, map_mul, MulAut.conj_apply, split_conjugation]

theorem pair_split (m : ℕ) (r : Index) (a : CoefficientField m) :
    toSplitGroup m (pair m r a) = pairWord m (root false r) (pairSolution m a) := by
  rcases r with ⟨p,i⟩
  cases p
  · change toSplitGroup m (NormalizerPresentation.weyl m opposition *
      (PositiveTables.pair m i a : Model m) * (NormalizerPresentation.weyl m opposition)⁻¹) = _
    rw [map_mul, map_mul, map_inv, PositiveTables.pair_split]
    have he := pairWord_conj m opposition (true,i) (pairSolution m a)
    have hr : root false (true,i) =
        (fun j => ((rootBlocks .positive).roots (.inl (i,j))).val) := rfl
    rw [hr] at he
    simpa only [action_opposition, Bool.not_true, MulAut.conj_apply, SignedGeometry.root, SignedGeometry.positiveRoot, if_true] using he
  · exact PositiveTables.pair_split i a

theorem quartet_split (m : ℕ) (r : Index) (a b : CoefficientField m) :
    toSplitGroup m (quartet m r a b) =
      quartetWord m (root true r) (PositiveTables.quartetParameters a b) := by
  rcases r with ⟨p,i⟩
  cases p
  · change toSplitGroup m (NormalizerPresentation.weyl m opposition *
      (PositiveTables.quartet m i a b : Model m) * (NormalizerPresentation.weyl m opposition)⁻¹) = _
    rw [map_mul, map_mul, map_inv, PositiveTables.quartet_split]
    have he := quartetWord_conj m opposition (true,i) (PositiveTables.quartetParameters a b)
    have hr : root true (true,i) =
        (fun j => ((rootBlocks .positive).roots (.inr (i,j))).val) := rfl
    rw [hr] at he
    simpa only [action_opposition, Bool.not_true, MulAut.conj_apply, SignedGeometry.root, SignedGeometry.positiveRoot, if_true] using he
  · exact PositiveTables.quartet_split i a b

/-- The complete signed type VI table has identity parameter transport. -/
theorem weyl_pair (m : ℕ) (w : Weyl) (r : Index) (a : CoefficientField m) :
    NormalizerPresentation.weyl m w * pair m r a * (NormalizerPresentation.weyl m w)⁻¹ =
      pair m (action false w r) a := by
  apply toSplitGroup_injective m
  rw [map_mul, map_mul, map_inv, pair_split, pair_split]
  exact pairWord_conj m w r _

/-- Both Suzuki coordinates are preserved, with their nonlinear product law. -/
theorem weyl_quartet (m : ℕ) (w : Weyl) (r : Index) (a b : CoefficientField m) :
    NormalizerPresentation.weyl m w * quartet m r a b * (NormalizerPresentation.weyl m w)⁻¹ =
      quartet m (action true w r) a b := by
  apply toSplitGroup_injective m
  rw [map_mul, map_mul, map_inv, quartet_split, quartet_split]
  exact quartetWord_conj m w r _

private theorem reflection_eq_weylLift (m : ℕ) (s : LargeLocalSeeds.Side) :
    RootPresentationRecognition.reflection m s = Parabolics.Binary.FixedGeometry.weylLift m s := by
  apply toSplitGroup_injective m
  rw [reflection_split, Parabolics.Binary.FixedGeometry.toSplitGroup_weylLift]

theorem reflection_pair (m : ℕ) (s : Bool) (r : Index) (a : CoefficientField m) :
    RootPresentationRecognition.reflection m (NormalizerPresentation.side s) * pair m r a *
      (RootPresentationRecognition.reflection m (NormalizerPresentation.side s))⁻¹ =
        pair m (step false s r) a := by
  simpa only [NormalizerPresentation.weyl_simple, action_simple, reflection_apply, reflection_eq_weylLift] using
    weyl_pair m (simple s) r a

theorem reflection_quartet (m : ℕ) (s : Bool) (r : Index) (a b : CoefficientField m) :
    RootPresentationRecognition.reflection m (NormalizerPresentation.side s) * quartet m r a b *
      (RootPresentationRecognition.reflection m (NormalizerPresentation.side s))⁻¹ =
        quartet m (step true s r) a b := by
  simpa only [NormalizerPresentation.weyl_simple, action_simple, reflection_apply, reflection_eq_weylLift] using
    weyl_quartet m (simple s) r a b

/-- Each signed whole root is evaluated from the same positive root carrier. -/
def rootHom (m : ℕ) (p : Bool) (i : PositiveTables.Root) :
    AngularPresentation.Parameter m i →* Model m :=
  (signConj m p).toMonoidHom.comp (AngularPresentation.nativeRoot m i)

theorem rootHom_injective (m : ℕ) (p : Bool) (i : PositiveTables.Root) :
    Function.Injective (rootHom m p i) :=
  (signConj m p).injective.comp Subtype.val_injective

@[simp] theorem rootHom_pair (m : ℕ) (p : Bool) (i : Fin 4) (a : CoefficientField m) :
    rootHom m p (.inl i) (PositiveTables.rootChartEquiv m (.inl i) a) = pair m (p,i) a := rfl

@[simp] theorem rootHom_quartet (m : ℕ) (p : Bool) (i : Fin 4) (a b : CoefficientField m) :
    rootHom m p (.inr i) (PositiveTables.rootChartEquiv m (.inr i) (a,b)) = quartet m (p,i) a b := rfl

/-- The actual signed root subgroup of the full model. -/
abbrev rootGroup (m : ℕ) (p : Bool) (i : PositiveTables.Root) := (rootHom m p i).range

/-- Both signed root kernels are proved trivial, including at field two. -/
def rootEquiv (m : ℕ) (p : Bool) (i : PositiveTables.Root) :
    AngularPresentation.Parameter m i ≃* rootGroup m p i :=
  MonoidHom.ofInjective (rootHom_injective m p i)


/-- The signed first pair is the existing Gauss chart, with the same parameter. -/
theorem pair_simple (m : ℕ) (p : Bool) (a : CoefficientField m) :
    pair m (p,0) a = linear m p a := by
  have hp : pair m (true,0) a = linear m true a := by
    have hr : root false (true,0) = linearRoots true := by
      funext j
      change Fin 2 at j
      fin_cases j <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
        norm_num [root, positiveRoot, rootBlocks_roots_val, RootPartition.index,
          RootPartition.pairRow, RootPartition.table, linearRoots, signedRoot,
          Theory.AlgebraicGroup.StandardRootSystem.typeF4SimpleRootIndex_val,
          Theory.AlgebraicGroup.StandardRootSystem.typeF4SimpleRoot,
          Matrix.cons_val_two, Matrix.cons_val_three]
    apply toSplitGroup_injective m
    rw [pair_split, linear_split, hr]
    rfl
  cases p
  · apply (MulAut.conj (RootPresentationRecognition.reflection m .linear)).injective
    change RootPresentationRecognition.reflection m .linear * pair m (false,0) a *
      (RootPresentationRecognition.reflection m .linear)⁻¹ = _
    have hi : (RootPresentationRecognition.reflection m .linear)⁻¹ =
      RootPresentationRecognition.reflection m .linear :=
        inv_eq_of_mul_eq_one_right (RootPresentationRecognition.reflection_sq m .linear)
    calc
      _ = pair m (true,0) a := reflection_pair m false (false,0) a
      _ = linear m true a := hp
      _ = _ := by
        change _ = RootPresentationRecognition.reflection m .linear * linear m false a *
          (RootPresentationRecognition.reflection m .linear)⁻¹
        rw [hi]
        exact (reflection_linear false a).symm
  · exact hp

/-- The signed first quartet is the full existing two-parameter Suzuki chart. -/
theorem quartet_simple (m : ℕ) (p : Bool) (a b : CoefficientField m) :
    quartet m (p,0) a b = suzuki m p a b := by
  cases p
  · apply (MulAut.conj (RootPresentationRecognition.reflection m .suzuki)).injective
    change RootPresentationRecognition.reflection m .suzuki * quartet m (false,0) a b *
      (RootPresentationRecognition.reflection m .suzuki)⁻¹ = _
    have hi : (RootPresentationRecognition.reflection m .suzuki)⁻¹ =
      RootPresentationRecognition.reflection m .suzuki :=
        inv_eq_of_mul_eq_one_right (RootPresentationRecognition.reflection_sq m .suzuki)
    calc
      _ = quartet m (true,0) a b := reflection_quartet m true (false,0) a b
      _ = suzuki m true a b := PositiveTables.quartet_simple a b
      _ = _ := by
        change _ = RootPresentationRecognition.reflection m .suzuki * suzuki m false a b *
          (RootPresentationRecognition.reflection m .suzuki)⁻¹
        rw [hi]
        exact (reflection_suzuki a b).symm
  · exact PositiveTables.quartet_simple a b

abbrev simpleIndex : Bool → PositiveTables.Root
  | false => .inl 0
  | true => .inr 0

/-- The marked signed carriers are the actual fixed simple-block intersections. -/
theorem rootGroup_simple (m : ℕ) (p s : Bool) :
    rootGroup m p (simpleIndex s) = rootBlock m (NormalizerPresentation.side s) p := by
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    obtain ⟨v,rfl⟩ := (PositiveTables.rootChartEquiv m (simpleIndex s)).surjective a
    cases s
    · change CoefficientField m at v
      change rootHom m p (.inl 0) (PositiveTables.rootChartEquiv m (.inl 0) v) ∈ _
      rw [rootHom_pair, pair_simple]
      exact linear_mem p v
    · change CoefficientField m × CoefficientField m at v
      change rootHom m p (.inr 0) (PositiveTables.rootChartEquiv m (.inr 0) (v.1,v.2)) ∈ _
      rw [rootHom_quartet, quartet_simple]
      exact suzuki_mem p v.1 v.2
  · intro x hx
    cases s
    · obtain ⟨a,rfl⟩ := linear_cover p x hx
      refine ⟨PositiveTables.rootChartEquiv m (.inl 0) a, ?_⟩
      exact (rootHom_pair m p 0 a).trans (pair_simple m p a)
    · obtain ⟨a,b,rfl⟩ := suzuki_cover p x hx
      refine ⟨PositiveTables.rootChartEquiv m (.inr 0) (a,b), ?_⟩
      exact (rootHom_quartet m p 0 a b).trans (quartet_simple m p a b)

/-- The simple signed chart carrier is literally the native fixed intersection. -/
def simpleRootEquiv (m : ℕ) (p s : Bool) :
    rootBlock m (NormalizerPresentation.side s) p ≃* rootGroup m p (simpleIndex s) :=
  MulEquiv.subgroupCongr (rootGroup_simple m p s).symm

@[simp] theorem simpleRootEquiv_apply (m : ℕ) (p s : Bool)
    (a : rootBlock m (NormalizerPresentation.side s) p) :
    (simpleRootEquiv m p s a : Model m) = a := rfl

/-- The new signed atlas uses the same full Cartan and linear Gauss relation. -/
theorem pair_gauss (m : ℕ) (a : (CoefficientField m)ˣ) :
    RootPresentationRecognition.reflection m .linear * pair m (false,0) a =
      pair m (false,0) (a⁻¹ : (CoefficientField m)ˣ) * torus m (linearTau a) *
        pair m (true,0) (a⁻¹ : (CoefficientField m)ˣ) := by
  simpa only [pair_simple] using linear_gauss a

open LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData in
/-- Both reciprocal parameters and the full Gauss torus are retained literally. -/
theorem quartet_gauss (m : ℕ) (a b : CoefficientField m) (hn : norm a b ≠ 0) :
    RootPresentationRecognition.reflection m .suzuki * quartet m (false,0) a b =
      quartet m (false,0) (negativeFirst a b) (negativeSecond a b) *
        torus m (suzukiTau (Units.mk0 (norm a b) hn)) *
          quartet m (true,0) (positiveFirst a b) (positiveSecond a b) := by
  simpa only [quartet_simple] using suzuki_gauss a b hn

/-- The binary Suzuki block remains cyclic of order four at every signed position. -/
theorem binary_quartet_square (r : Index) :
    quartet 0 r 1 0 * quartet 0 r 1 0 = quartet 0 r 0 1 := by
  rw [quartet_mul]
  simp only [CharTwo.add_self_eq_zero, zero_add, map_one, mul_one]

theorem quartet_zero_one_ne_one (m : ℕ) (r : Index) : quartet m r 0 1 ≠ 1 := by
  intro h
  have he : ((0,1) : CoefficientField m × CoefficientField m) = (0,0) := by
    apply quartet_injective m r
    change quartet m r 0 1 = quartet m r 0 0
    rw [quartet_zero]
    exact h
  exact one_ne_zero (congrArg Prod.snd he)

theorem binary_quartet_square_ne_one (r : Index) :
    quartet 0 r 1 0 * quartet 0 r 1 0 ≠ 1 := by
  rw [binary_quartet_square]
  exact quartet_zero_one_ne_one 0 r

end ReeF4.RootPresentationRecognition.SignedCharts
