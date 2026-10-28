module

public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.RootComparison
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.GeckSpin.CliffordComparison
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.GeckSpin.Faithfulness.Coordinates
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.GeckSpin.Faithfulness.Points
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.GeckSpin.RootIntertwining.Actions

/-!
# Faithful Geck-to-Spin comparison from Clifford coordinates

The elements of the concrete Geck matrix group admitting compatible Spin actions
form a subgroup. The eight signed root identities make this subgroup the whole
Geck group. Faithfulness of conjugation on the comparison coordinates makes the
compatible Spin element unique, hence makes the assignment multiplicative.
Injectivity of the coordinate embedding proves injectivity of this group map.

The concrete coordinate-separation and signed root-action theorems discharge
every premise of this construction. Coefficient extension then gives precisely
`HasRootFormula` for every finite cubic binary field, including GF(8).
`exists_finite_comparison` proves the unconditional existence statement;
`finiteComparison` chooses such an injective homomorphism. Its root formulas
also identify its image and intertwine the actual graph-field automorphisms.

Sources: GLS3, §§1.12–1.14, Remarks 2.2.5 and §2.7
(`refs/KGroup/GLS3/Chapter1.tex` and `chapter2.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.BinaryDegree.CarrierTransport.GeckSpin
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.SimplyConnected Triality.SimplyConnected.Pinning
open RootPairing.SimpleGeckGroup

attribute [local instance] indexDecidableEq

variable (k : Type*) [Field k] [IsAlgClosed k]

/-- A faithful Clifford action and the eight literal root identities construct a
well-defined injective map out of the concrete Geck matrix group. -/
theorem exists_comparison_of_clifford [CharP k 2]
    (hι : Function.Injective (embedding k))
    (hfaith : ∀ x y : Points k,
      (∀ v, pointConjugation k x (embedding k v) =
        pointConjugation k y (embedding k v)) → x = y)
    (hp : ∀ i t, Intertwines k
      (positive (typeDRootPairing_baseEquiv 2 i) t) (positiveSimplePoint k i t))
    (hn : ∀ i t, Intertwines k
      (negative (typeDRootPairing_baseEquiv 2 i) t) (negativeSimplePoint k i t)) :
    ∃ e : SplitPoints k →* Points k, Function.Injective e ∧
      (∀ i t, e (positive (typeDRootPairing_baseEquiv 2 i) t) =
        positiveSimplePoint k i t) ∧
      (∀ i t, e (negative (typeDRootPairing_baseEquiv 2 i) t) =
        negativeSimplePoint k i t) := by
  let H : Subgroup (SplitPoints k) :=
    { carrier := {g | ∃ x, Intertwines k g x}
      one_mem' := ⟨1, intertwines_one k⟩
      mul_mem' := by
        rintro g h ⟨x, hx⟩ ⟨y, hy⟩
        exact ⟨x * y, Intertwines.mul k hx hy⟩
      inv_mem' := by
        rintro g ⟨x, hx⟩
        exact ⟨x⁻¹, Intertwines.inv k hx⟩ }
  have hgen : subgroup (typeDRootPairing_base 2) k ≤
      H.map (subgroup (typeDRootPairing_base 2) k).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro a ⟨⟨s, j⟩, t, rfl⟩
    obtain ⟨i, rfl⟩ := (typeDRootPairing_baseEquiv 2).surjective j
    cases s
    · exact ⟨negative _ t, ⟨_, hn i t⟩, rfl⟩
    · exact ⟨positive _ t, ⟨_, hp i t⟩, rfl⟩
  have hex (g : SplitPoints k) : ∃ x, Intertwines k g x := by
    obtain ⟨g', hg', he⟩ := hgen g.property
    have he' : g' = g := Subtype.ext he
    subst g'
    exact hg'
  have hu {g : SplitPoints k} {x y : Points k}
      (hx : Intertwines k g x) (hy : Intertwines k g y) : x = y :=
    hfaith x y (fun v => (hx v).trans (hy v).symm)
  choose e he using hex
  let E : SplitPoints k →* Points k :=
    { toFun := e
      map_one' := hu (he 1) (intertwines_one k)
      map_mul' g h := hu (he (g * h)) ((he g).mul k (he h)) }
  refine ⟨E, ?_, ?_, ?_⟩
  · intro g h hgh
    exact (he g).geck_unique k hι (by simpa only [show e h = e g from hgh.symm] using he h)
  · intro i t
    exact hu (he _) (hp i t)
  · intro i t
    exact hu (he _) (hn i t)

omit [IsAlgClosed k] in
/-- The coefficient extension on the concrete matrix group is injective. -/
theorem scalarExtension_injective {F : Type*} [Field F] (f : F →+* k) :
    Function.Injective (RootPairing.SimpleGeckGroup.map (b := typeDRootPairing_base 2) f) := by
  intro g h he
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply f.injective
  exact congrArg (fun x : SplitPoints k => x.val.val i j) he

/-- Specialization to every finite binary cubic field, including GF(8).
The two independent Clifford comparison obligations remain explicit. -/
theorem exists_finite_comparison_of_clifford [CharP k 2]
    (hι : Function.Injective (embedding k))
    (hfaith : ∀ x y : Points k,
      (∀ v, pointConjugation k x (embedding k v) =
        pointConjugation k y (embedding k v)) → x = y)
    (hp : ∀ i t, Intertwines k
      (positive (typeDRootPairing_baseEquiv 2 i) t) (positiveSimplePoint k i t))
    (hn : ∀ i t, Intertwines k
      (negative (typeDRootPairing_baseEquiv 2 i) t) (negativeSimplePoint k i t))
    {n : ℕ} {hpos : 0 < n}
    (f : Triality.Standard.ExtensionField (Triality.Standard.binaryParameters n hpos) →+* k) :
    ∃ e : Triality.Standard.SplitGroup (Triality.Standard.binaryParameters n hpos) →* Points k,
      Function.Injective e ∧ HasRootFormula f e := by
  obtain ⟨e, he, hep, hen⟩ := exists_comparison_of_clifford k hι hfaith hp hn
  refine ⟨e.comp (RootPairing.SimpleGeckGroup.map f),
    he.comp (scalarExtension_injective k f), ?_, ?_⟩
  · intro i t
    change e (RootPairing.SimpleGeckGroup.map f _) = _
    rw [map_positive, hep]
  · intro i t
    change e (RootPairing.SimpleGeckGroup.map f _) = _
    rw [map_negative, hen]

variable [CharP k 2]

/-- The finite split Geck group embeds into the concrete Clifford Spin points,
with both literal signed simple-root formulas, for every positive exponent.
In particular, `n = 1` gives the comparison over GF(8). -/
theorem exists_finite_comparison {n : ℕ} {hn : 0 < n}
    (f : Triality.Standard.ExtensionField (Triality.Standard.binaryParameters n hn) →+* k) :
    ∃ e : Triality.Standard.SplitGroup (Triality.Standard.binaryParameters n hn) →* Points k,
      Function.Injective e ∧ HasRootFormula f e :=
  exists_finite_comparison_of_clifford k (embedding_injective k)
    (pointConjugation_ext k) (RootIntertwining.signed_intertwines k true)
    (RootIntertwining.signed_intertwines k false) f

/-- A faithful comparison of the literal finite Geck and Clifford Spin groups. -/
def finiteComparison {n : ℕ} {hn : 0 < n}
    (f : Triality.Standard.ExtensionField (Triality.Standard.binaryParameters n hn) →+* k) :
    Triality.Standard.SplitGroup (Triality.Standard.binaryParameters n hn) →* Points k :=
  (exists_finite_comparison k f).choose

theorem finiteComparison_injective {n : ℕ} {hn : 0 < n}
    (f : Triality.Standard.ExtensionField (Triality.Standard.binaryParameters n hn) →+* k) :
    Function.Injective (finiteComparison k f) :=
  (exists_finite_comparison k f).choose_spec.1

theorem finiteComparison_hasRootFormula {n : ℕ} {hn : 0 < n}
    (f : Triality.Standard.ExtensionField (Triality.Standard.binaryParameters n hn) →+* k) :
    HasRootFormula f (finiteComparison k f) :=
  (exists_finite_comparison k f).choose_spec.2

/-- The comparison keeps the numbered positive root and its parameter. -/
@[simp] theorem finiteComparison_positive {n : ℕ} {hn : 0 < n}
    (f : Triality.Standard.ExtensionField (Triality.Standard.binaryParameters n hn) →+* k)
    (i : Fin 4) (t : Triality.Standard.ExtensionField (Triality.Standard.binaryParameters n hn)) :
    finiteComparison k f (positive (typeDRootPairing_baseEquiv 2 i) t) =
      positiveSimplePoint k i (f t) :=
  (finiteComparison_hasRootFormula k f).1 i t

/-- The comparison keeps the numbered negative root and its parameter. -/
@[simp] theorem finiteComparison_negative {n : ℕ} {hn : 0 < n}
    (f : Triality.Standard.ExtensionField (Triality.Standard.binaryParameters n hn) →+* k)
    (i : Fin 4) (t : Triality.Standard.ExtensionField (Triality.Standard.binaryParameters n hn)) :
    finiteComparison k f (negative (typeDRootPairing_baseEquiv 2 i) t) =
      negativeSimplePoint k i (f t) :=
  (finiteComparison_hasRootFormula k f).2 i t

/-- Its image is exactly the subgroup generated by the rational simple roots. -/
theorem finiteComparison_range {n : ℕ} {hn : 0 < n}
    (f : Triality.Standard.ExtensionField (Triality.Standard.binaryParameters n hn) →+* k) :
    (finiteComparison k f).range = rationalSimpleSubgroup f :=
  (finiteComparison_hasRootFormula k f).range_eq

/-- The comparison intertwines the prescribed diagram-then-field actions. -/
theorem finiteComparison_graphField {n : ℕ} {hn : 0 < n}
    (f : Triality.Standard.ExtensionField (Triality.Standard.binaryParameters n hn) →+* k)
    (g : Triality.Standard.SplitGroup (Triality.Standard.binaryParameters n hn)) :
    finiteComparison k f (Triality.Standard.graphFieldAutomorphism
      (Triality.Standard.binaryParameters n hn) g) =
      GraphField.sigma k n (finiteComparison k f g) :=
  (finiteComparison_hasRootFormula k f).graphField_intertwines g

end Triality.BinaryDegree.CarrierTransport.GeckSpin
