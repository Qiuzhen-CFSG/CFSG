module

public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.Reduction
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.MixedCoordinates
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.Homogeneous
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.MixedExhaustion
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointRestriction.LocalCatalogue.ExtensionClasses.MixedModels

/-!
# Classification of central-quadratic binary SL₃(4) extensions

For the two concrete six-dimensional constituents, every central-quadratic
block extension is equivalent, by an actual change of binary linear section,
to one of the following explicit twelve-dimensional models:

* a direct sum in either homogeneous orientation;
* the two-parameter family `p Q(g) + q R(g)` applied after coordinatewise
  squaring in the natural-by-dual orientation;
* its inverse-transpose pullback in the reverse mixed orientation.

Here `(p,q)` ranges over F₄ × F₄, and Q and R are the global matrix formulas
in `MixedCoordinates`. Precisely `(0,0)` splits in either mixed orientation.
The predicate `BlockCocycle.IsSplit` means that the actual quotient projection
has an equivariant binary linear section. The finite catalogue retains formulas
on every group element and explicit values on the proved transvection generators.
The parameter set classifies extensions with their specified endpoints; no
assertion of pairwise nonisomorphism of the underlying representations is needed.

The proof first kills the central cross block by a section change. The
homogeneous calculation and the independent mixed exhaustion and model
construction then classify the normalized extensions. Inverse transpose
handles the other two orientations. `ExtensionClass.classify` discharges the
normalization premise and supplies both the actual equivalence and the splitting
criterion for the original extension.

This intrinsic extension calculation supports James (1973), Lemma 8.3, cited
in Aschbacher–Smith H.12.1, printed pp.393–394. The point restriction on p.394
is an extension of the natural module by its dual; splitting is not assumed.
Constituent completeness, passage from arbitrary modules to block coordinates,
and the full Mathieu classification are separate results.
-/

@[expose] public noncomputable section

namespace Representation.SL3FourLocalCatalogue
open ExtensionCoordinates

private lemma binary_add_self {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (v : M) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 by decide, zero_smul]

namespace BlockCocycle
variable {a b : Constituent}

/-- The quotient projection of the extension admits an equivariant binary linear section. -/
def IsSplit (c : BlockCocycle a b) : Prop :=
  ∃ s : W →ₗ[ZMod 2] W × W,
    (LinearMap.snd (ZMod 2) W W).comp s = LinearMap.id ∧
    ∀ g : SL, (c.representation g).comp s = s.comp (constituent b g)

/-- Splitting the actual quotient map is equivalent to killing the cross block
by a change of binary linear section. -/
lemma isSplit_iff_coboundary (c : BlockCocycle a b) :
    c.IsSplit ↔ ∃ f : W →ₗ[ZMod 2] W, ∀ g : SL,
      c.value g + f.comp (constituent b g) = (constituent a g).comp f := by
  constructor
  · rintro ⟨s, hs, he⟩
    refine ⟨(LinearMap.fst (ZMod 2) W W).comp s, fun g => ?_⟩
    apply LinearMap.ext
    intro v
    have hv := congrArg Prod.fst (LinearMap.congr_fun (he g) v)
    have hvs : (s v).2 = v := LinearMap.congr_fun hs v
    change (constituent a g) (s v).1 + c.value g (s v).2 =
      (s ((constituent b g) v)).1 at hv
    rw [hvs] at hv
    change c.value g v + (s ((constituent b g) v)).1 = (constituent a g) (s v).1
    have hz := binary_add_self (c.value g v)
    linear_combination (norm := abel) -hv + hz
  · rintro ⟨f, hf⟩
    refine ⟨f.prod LinearMap.id, rfl, fun g => ?_⟩
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · have hv := LinearMap.congr_fun (hf g) v
      change c.value g v + f ((constituent b g) v) = (constituent a g) (f v) at hv
      change (constituent a g) (f v) + c.value g v = f ((constituent b g) v)
      have hz := binary_add_self (c.value g v)
      linear_combination (norm := abel) -hv + hz
    · rfl

lemma zero_isSplit (a b : Constituent) : (zero a b).IsSplit := by
  apply (isSplit_iff_coboundary _).mpr
  exact ⟨0, fun g => by simp [zero]⟩

/-- Changing a linear section preserves splitting of the actual extension. -/
lemma isSplit_iff_of_coboundary (c d : BlockCocycle a b) (f : W →ₗ[ZMod 2] W)
    (hf : ∀ g : SL, c.value g + f.comp (constituent b g) =
      (constituent a g).comp f + d.value g) : c.IsSplit ↔ d.IsSplit := by
  rw [isSplit_iff_coboundary, isSplit_iff_coboundary]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u - f, fun g => ?_⟩
    simp only [LinearMap.sub_comp, LinearMap.comp_sub]
    linear_combination (norm := abel) hu g - hf g
  · rintro ⟨u, hu⟩
    refine ⟨u + f, fun g => ?_⟩
    simp only [LinearMap.add_comp, LinearMap.comp_add]
    linear_combination (norm := abel) hu g + hf g

end BlockCocycle

namespace ExtensionClass

/-- One split parameter in a homogeneous orientation; two F₄ parameters in a mixed one. -/
def Parameter : Constituent → Constituent → Type
  | .natural, .natural => Unit
  | .natural, .dual => F × F
  | .dual, .natural => F × F
  | .dual, .dual => Unit

instance (a b : Constituent) : Fintype (Parameter a b) := by
  cases a <;> cases b <;> dsimp [Parameter] <;> infer_instance

instance (a b : Constituent) : DecidableEq (Parameter a b) := by
  cases a <;> cases b <;> dsimp [Parameter] <;> infer_instance

instance (a : Constituent) : Subsingleton (Parameter a a) := by
  cases a <;> dsimp [Parameter] <;> infer_instance

/-- The structural list has one homogeneous or sixteen mixed parameters. -/
lemma card_parameter (a b : Constituent) :
    Fintype.card (Parameter a b) = if a = b then 1 else 16 := by
  cases a <;> cases b <;> decide +kernel

/-- The parameter of the split extension in each orientation. -/
def splitParameter : (a b : Constituent) → Parameter a b
  | .natural, .natural => ()
  | .natural, .dual => (0, 0)
  | .dual, .natural => (0, 0)
  | .dual, .dual => ()

/-- Explicit block models: zero in the homogeneous cases, and the two mixed
formulas or their inverse-transpose pullbacks in the mixed cases. -/
def model : (a b : Constituent) → Parameter a b → BlockCocycle a b
  | .natural, .natural, _ => BlockCocycle.zero .natural .natural
  | .natural, .dual, r => mixedCocycle r.1 r.2
  | .dual, .natural, r => (mixedCocycle r.1 r.2).graphTwist
  | .dual, .dual, _ => BlockCocycle.zero .dual .dual

lemma model_value_z (a b : Constituent) (r : Parameter a b) :
    (model a b r).value z = 0 := by
  cases a <;> cases b
  · rfl
  · exact mixedCocycle_value_z r.1 r.2
  · exact BlockCocycle.graphTwist_normalized _ (mixedCocycle_value_z r.1 r.2)
  · rfl

lemma model_isCentral (a b : Constituent) (r : Parameter a b) :
    (model a b r).IsCentral :=
  BlockCocycle.isCentral_of_value_z_eq_zero _ (model_value_z a b r)

lemma model_centralQuadratic (a b : Constituent) (r : Parameter a b) :
    CentralQuadratic (model a b r).representation :=
  (model a b r).centralQuadratic_iff.mpr (model_isCentral a b r)

lemma model_faithful (a b : Constituent) (r : Parameter a b) :
    Function.Injective (model a b r).representation :=
  (model a b r).representation_faithful

lemma model_finrank : Module.finrank (ZMod 2) (W × W) = 12 := split_finrank

lemma model_splitParameter (a b : Constituent) :
    model a b (splitParameter a b) = BlockCocycle.zero a b := by
  cases a <;> cases b
  · rfl
  · exact mixedCocycle_zero
  · apply BlockCocycle.ext_transvections
    intro i j hij t
    exact mixedValue_zero _
  · rfl

/-- On every group element, the natural-by-dual cross block is the published
sum of the symmetric-square and binary-dual formulas. -/
lemma model_natural_dual_value (r : F × F) (g : SL) :
    (model .natural .dual r).value g = mixedValue r.1 r.2 g := rfl

/-- The reverse mixed orientation is given on every element by inverse transpose. -/
lemma model_dual_natural_value (r : F × F) (g : SL) :
    (model .dual .natural r).value g =
      mixedValue r.1 r.2 (Matrix.SpecialLinearGroup.inverseTranspose g) := rfl

/-- The explicit natural-by-dual cross block on every elementary generator. -/
lemma model_natural_dual_transvection (r : F × F) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (t : F) (v : W) :
    (model .natural .dual r).value (Matrix.SpecialLinearGroup.transvection hij t) v =
      r.1 • Pi.single i (t^2 * (v k)^2) + r.2 • Pi.single k (t * (v i)^2) :=
  mixedValue_transvection hij hik hjk r.1 r.2 t v

private lemma inverseTranspose_transvection {i j : Fin 3} (hij : i ≠ j) (t : F) :
    Matrix.SpecialLinearGroup.inverseTranspose (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.transvection hij.symm t := by
  apply Subtype.ext
  change ((Matrix.SpecialLinearGroup.transvection hij t)⁻¹).val.transpose = _
  rw [Matrix.SpecialLinearGroup.transvection_inv, CharTwo.neg_eq]
  simp only [Matrix.SpecialLinearGroup.transvection_coe, Matrix.transpose_add,
    Matrix.transpose_one, Matrix.transpose_single]

/-- The explicit reverse mixed cross block on the same proved generating family. -/
lemma model_dual_natural_transvection (r : F × F) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (t : F) (v : W) :
    (model .dual .natural r).value (Matrix.SpecialLinearGroup.transvection hij t) v =
      r.1 • Pi.single j (t^2 * (v k)^2) + r.2 • Pi.single k (t * (v j)^2) := by
  rw [model_dual_natural_value, inverseTranspose_transvection]
  exact mixedValue_transvection hij.symm hjk hik r.1 r.2 t v

private lemma comparison_of_transvections {a b : Constituent}
    (c d : BlockCocycle a b) (f : W →ₗ[ZMod 2] W)
    (h : ∀ (i j : Fin 3) (hij : i ≠ j) (t : F),
      c.value (Matrix.SpecialLinearGroup.transvection hij t) +
        f.comp (constituent b (Matrix.SpecialLinearGroup.transvection hij t)) =
      (constituent a (Matrix.SpecialLinearGroup.transvection hij t)).comp f +
        d.value (Matrix.SpecialLinearGroup.transvection hij t)) :
    ∀ g : SL, c.value g + f.comp (constituent b g) =
      (constituent a g).comp f + d.value g := by
  have he : c.shift f = d := by
    apply BlockCocycle.ext_transvections
    intro i j hij t
    have hh := h i j hij t
    have hz := binary_add_self
      ((constituent a (Matrix.SpecialLinearGroup.transvection hij t)).comp f)
    change c.value _ + (constituent a _).comp f + f.comp (constituent b _) = _
    linear_combination (norm := abel) hh + hz
  intro g
  have hh := congrArg (fun e : BlockCocycle a b => e.value g) he
  change c.value g + (constituent a g).comp f + f.comp (constituent b g) = d.value g at hh
  have hz := binary_add_self ((constituent a g).comp f)
  linear_combination (norm := abel) hh - hz

private lemma normalized_mixed (c : BlockCocycle .natural .dual) (hc : c.value z = 0) :
    ∃ (p q : F) (f : W →ₗ[ZMod 2] W), ∀ g : SL,
      c.value g + f.comp (constituent .dual g) =
        (constituent .natural g).comp f + (mixedCocycle p q).value g := by
  obtain ⟨p, q, f, hf⟩ := c.exists_mixed_transvection_coboundary hc
  exact ⟨p, q, f, comparison_of_transvections c (mixedCocycle p q) f hf⟩

private lemma normalized_classification {a b : Constituent}
    (c : BlockCocycle a b) (hc : c.value z = 0) :
    ∃ (r : Parameter a b) (f : W →ₗ[ZMod 2] W), ∀ g : SL,
      c.value g + f.comp (constituent b g) =
        (constituent a g).comp f + (model a b r).value g := by
  cases a <;> cases b
  · obtain ⟨f, hf⟩ := c.normalized_natural_coboundary hc
    exact ⟨(), f, fun g => by simpa only [model, BlockCocycle.zero, add_zero] using hf g⟩
  · obtain ⟨p, q, f, hf⟩ := normalized_mixed c hc
    exact ⟨(p, q), f, hf⟩
  · obtain ⟨p, q, f, hf⟩ := normalized_mixed c.graphTwist (c.graphTwist_normalized hc)
    refine ⟨(p, q), f, fun g => ?_⟩
    have hh := hf (Matrix.SpecialLinearGroup.inverseTranspose g)
    change c.value (Matrix.SpecialLinearGroup.inverseTranspose
      (Matrix.SpecialLinearGroup.inverseTranspose g)) +
      f.comp (constituent .dual (Matrix.SpecialLinearGroup.inverseTranspose g)) =
      (constituent .natural (Matrix.SpecialLinearGroup.inverseTranspose g)).comp f +
      (mixedCocycle p q).value (Matrix.SpecialLinearGroup.inverseTranspose g) at hh
    rw [SL3FourNaturalDual.inverseTranspose_involutive,
      ← constituent_flip .dual, ← constituent_flip .natural] at hh
    exact hh
  · obtain ⟨f, hf⟩ := c.graphTwist.normalized_natural_coboundary (c.graphTwist_normalized hc)
    refine ⟨(), f, fun g => ?_⟩
    have hh := hf (Matrix.SpecialLinearGroup.inverseTranspose g)
    change c.value (Matrix.SpecialLinearGroup.inverseTranspose
      (Matrix.SpecialLinearGroup.inverseTranspose g)) +
      f.comp (constituent .natural (Matrix.SpecialLinearGroup.inverseTranspose g)) =
      (constituent .natural (Matrix.SpecialLinearGroup.inverseTranspose g)).comp f at hh
    rw [SL3FourNaturalDual.inverseTranspose_involutive, ← constituent_flip .natural] at hh
    simpa only [model, BlockCocycle.zero, add_zero, Constituent.flip] using hh

/-- Every central-quadratic cocycle is a section change of one explicit model,
with the comparison valid on the entire group. All normalization premises are discharged. -/
theorem exists_model_coboundary {a b : Constituent}
    (c : BlockCocycle a b) (hc : c.IsCentral) :
    ∃ (r : Parameter a b) (f : W →ₗ[ZMod 2] W), ∀ g : SL,
      c.value g + f.comp (constituent b g) =
        (constituent a g).comp f + (model a b r).value g := by
  obtain ⟨r, f, hf⟩ := normalized_classification c.normalize (c.normalize_value_z hc)
  refine ⟨r, c.value z + f, fun g => ?_⟩
  have hh := hf g
  change c.value g + (constituent a g).comp (c.value z) +
    (c.value z).comp (constituent b g) + f.comp (constituent b g) =
    (constituent a g).comp f + (model a b r).value g at hh
  simp only [LinearMap.add_comp, LinearMap.comp_add]
  have hz := binary_add_self ((constituent a g).comp (c.value z))
  linear_combination (norm := abel) hh - hz

/-- Exhaustive coverage by actual binary representation equivalences, for every
ordered pair of the two concrete constituents. -/
theorem exists_model_equiv {a b : Constituent}
    (c : BlockCocycle a b) (hc : c.IsCentral) :
    ∃ r : Parameter a b, Nonempty (c.representation.Equiv (model a b r).representation) := by
  obtain ⟨r, f, hf⟩ := exists_model_coboundary c hc
  exact ⟨r, ⟨c.equivOfCoboundary (model a b r) f hf⟩⟩

/-- Precisely the distinguished parameter splits as an extension. In either
mixed orientation every other pair is a genuine nonsplit extension. -/
theorem model_isSplit_iff (a b : Constituent) (r : Parameter a b) :
    (model a b r).IsSplit ↔ r = splitParameter a b := by
  constructor
  · intro h
    cases a <;> cases b
    · exact Subsingleton.elim _ _
    · have hh := (BlockCocycle.isSplit_iff_coboundary _).mp h
      exact Prod.ext ((mixedValue_coboundary_iff r.1 r.2).mp hh).1
        ((mixedValue_coboundary_iff r.1 r.2).mp hh).2
    · obtain ⟨f, hf⟩ := (BlockCocycle.isSplit_iff_coboundary _).mp h
      have hh : ∀ g : SL, mixedValue r.1 r.2 g + f.comp (constituent .dual g) =
          (constituent .natural g).comp f := by
        intro g
        have he := hf (Matrix.SpecialLinearGroup.inverseTranspose g)
        change mixedValue r.1 r.2 (Matrix.SpecialLinearGroup.inverseTranspose
          (Matrix.SpecialLinearGroup.inverseTranspose g)) +
          f.comp (constituent .natural (Matrix.SpecialLinearGroup.inverseTranspose g)) =
          (constituent .dual (Matrix.SpecialLinearGroup.inverseTranspose g)).comp f at he
        rw [SL3FourNaturalDual.inverseTranspose_involutive,
          ← constituent_flip .natural, ← constituent_flip .dual] at he
        exact he
      have hp := mixedValue_parameters_eq_zero_of_coboundary r.1 r.2 f hh
      exact Prod.ext hp.1 hp.2
    · exact Subsingleton.elim _ _
  · intro h
    rw [h, model_splitParameter]
    exact BlockCocycle.zero_isSplit a b

/-- The full finite extension classification, including the splitting alternative
for the original extension and an actual representation equivalence. -/
theorem classify {a b : Constituent} (c : BlockCocycle a b) (hc : c.IsCentral) :
    ∃ r : Parameter a b,
      Nonempty (c.representation.Equiv (model a b r).representation) ∧
      (c.IsSplit ↔ r = splitParameter a b) := by
  obtain ⟨r, f, hf⟩ := exists_model_coboundary c hc
  exact ⟨r, ⟨c.equivOfCoboundary (model a b r) f hf⟩,
    (c.isSplit_iff_of_coboundary (model a b r) f hf).trans (model_isSplit_iff a b r)⟩

/-- Every central-quadratic homogeneous extension admits an equivariant section. -/
theorem homogeneous_isSplit (a : Constituent) (c : BlockCocycle a a) (hc : c.IsCentral) :
    c.IsSplit := by
  obtain ⟨r, _, hs⟩ := classify c hc
  exact hs.mpr (Subsingleton.elim _ _)

/-- A split parameter gives the actual direct-sum representation. -/
lemma model_split_representation (a b : Constituent) :
    (model a b (splitParameter a b)).representation = splitRepresentation a b := by
  rw [model_splitParameter, BlockCocycle.zero_representation]

/-- The unique homogeneous model is split, so every central-quadratic
self-extension of either constituent is equivalent to its direct sum. -/
theorem homogeneous_split_equiv (a : Constituent) (c : BlockCocycle a a)
    (hc : c.IsCentral) : Nonempty (c.representation.Equiv (splitRepresentation a a)) := by
  obtain ⟨r, he⟩ := exists_model_equiv c hc
  have hr : r = splitParameter a a := by cases a <;> exact Subsingleton.elim _ _
  rwa [hr, model_split_representation] at he


end ExtensionClass
end Representation.SL3FourLocalCatalogue
