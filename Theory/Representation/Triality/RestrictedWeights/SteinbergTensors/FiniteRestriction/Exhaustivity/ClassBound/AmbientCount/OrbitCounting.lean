module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Twisted orbit counting

For an action of a group `W`, a map taking each point into its own orbit
has the same transporter count as the stabilizer count. Choosing a transporter
at each point identifies the two sets of pairs; Burnside's bijection then
identifies them with `(X/W) × W`. This bijection needs no finiteness assumption.

Finite twisted kernels give finiteness of the orbit space. For a set of stable
parameters whose fibers are exactly the orbits, restricting to its inverse
image gives the inequality used by the ambient D4 class-count assembly.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, 14.7.
-/

open scoped BigOperators
public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount.TwistedCount
variable {W X : Type*} [Group W] [MulAction W X]

/-- Change each transporter to the corresponding stabilizer. -/
def transporterEquivStabilizer (σ : X → X) (x : X) (a : W)
    (ha : σ x = a • x) : {w : W // σ x = w • x} ≃ MulAction.stabilizer W x where
  toFun w := ⟨a⁻¹ * w, by
    change (a⁻¹ * w.val) • x = x
    rw [mul_smul, ← w.property, ha, inv_smul_smul]⟩
  invFun w := ⟨a * w, by
    rw [mul_smul, show (w : W) • x = x from w.property, ha]⟩
  left_inv w := Subtype.ext (by simp)
  right_inv w := Subtype.ext (by simp)

/-- Twisted transporter counting as an actual bijection, without finiteness. -/
def twistedPairsEquiv (σ : X → X) (hσ : ∀ x, ∃ w : W, σ x = w • x) :
    (Σ w : W, {x : X // σ x = w • x}) ≃
      MulAction.orbitRel.Quotient W X × W := by
  let e₁ : (Σ w : W, {x : X // σ x = w • x}) ≃
      (Σ x : X, {w : W // σ x = w • x}) :=
    calc
      _ ≃ {p : W × X // σ p.2 = p.1 • p.2} :=
        (Equiv.subtypeProdEquivSigmaSubtype _).symm
      _ ≃ {p : X × W // σ p.1 = p.2 • p.1} :=
        (Equiv.prodComm W X).subtypeEquiv fun _ => Iff.rfl
      _ ≃ _ := Equiv.subtypeProdEquivSigmaSubtype (fun (x : X) (w : W) => σ x = w • x)
  let e₂ : (Σ x : X, {w : W // σ x = w • x}) ≃
      (Σ x : X, MulAction.stabilizer W x) :=
    Equiv.sigmaCongrRight fun x =>
      transporterEquivStabilizer σ x (hσ x).choose (hσ x).choose_spec
  let e₃ : (Σ x : X, MulAction.stabilizer W x) ≃
      (Σ w : W, MulAction.fixedBy X w) :=
    calc
      _ ≃ {p : X × W // p.2 • p.1 = p.1} :=
        (Equiv.subtypeProdEquivSigmaSubtype (fun (x : X) (w : W) => w • x = x)).symm
      _ ≃ {p : W × X // p.1 • p.2 = p.2} :=
        (Equiv.prodComm X W).subtypeEquiv fun _ => Iff.rfl
      _ ≃ _ := Equiv.subtypeProdEquivSigmaSubtype (fun (w : W) (x : X) => w • x = x)
  exact e₁.trans (e₂.trans (e₃.trans (MulAction.sigmaFixedByEquivOrbitsProdGroup W X)))

/-- Finite twisted kernels imply a finite orbit space. -/
theorem finite_orbits [Finite W] (σ : X → X)
    (hσ : ∀ x, ∃ w : W, σ x = w • x)
    (hfin : ∀ w : W, Finite {x : X // σ x = w • x}) :
    Finite (MulAction.orbitRel.Quotient W X) := by
  let := hfin
  let : Finite (MulAction.orbitRel.Quotient W X × W) :=
    Finite.of_equiv _ (twistedPairsEquiv σ hσ)
  exact Finite.of_injective (fun x : MulAction.orbitRel.Quotient W X => (x, (1 : W)))
    (fun _ _ h => congrArg Prod.fst h)

/-- Steinberg 14.7 after restricting to the stable orbits. -/
theorem sum_card_twisted [Fintype W] (σ : X → X)
    (hσ : ∀ x, ∃ w : W, σ x = w • x)
    (hfin : ∀ w : W, Finite {x : X // σ x = w • x}) :
    (∑ w : W, Nat.card {x : X // σ x = w • x}) =
      Nat.card (MulAction.orbitRel.Quotient W X) * Nat.card W := by
  let := hfin
  rw [← Nat.card_sigma, Nat.card_congr (twistedPairsEquiv σ hσ), Nat.card_prod]

variable {C : Type*}

/-- A surjective parameter map with orbit fibers identifies the orbit space. -/
def orbitEquivParameters (f : X → C) (hsurj : Function.Surjective f)
    (hf : ∀ x y, f x = f y ↔ ∃ w : W, w • x = y) :
    MulAction.orbitRel.Quotient W X ≃ C :=
  Equiv.ofBijective
    (Quotient.lift f (by
      intro x y h
      obtain ⟨w, hw⟩ := h
      exact ((hf y x).mpr ⟨w, hw⟩).symm))
    ⟨by
      intro a b
      refine Quotient.inductionOn₂ a b ?_
      intro x y h
      apply Quotient.sound
      exact (hf y x).mp h.symm,
    fun c => by
      obtain ⟨x, rfl⟩ := hsurj c
      exact ⟨Quotient.mk _ x, rfl⟩⟩

/-- Finite twisted kernels imply finitely many preserved orbit parameters. -/
theorem finite_parameters [Finite W] (f : X → C)
    (hsurj : Function.Surjective f)
    (hf : ∀ x y, f x = f y ↔ ∃ w : W, w • x = y)
    (σ : X → X) (hσ : ∀ x, f (σ x) = f x)
    (hfin : ∀ w : W, Finite {x : X // σ x = w • x}) : Finite C := by
  have horbit : ∀ x, ∃ w : W, σ x = w • x := by
    intro x
    obtain ⟨w, hw⟩ := (hf x (σ x)).mp (hσ x).symm
    exact ⟨w, hw.symm⟩
  let := finite_orbits σ horbit hfin
  exact Finite.of_equiv _ (orbitEquivParameters f hsurj hf)

/-- The exact twisted-kernel formula for a complete set of orbit parameters. -/
theorem sum_card_twisted_eq [Fintype W] (f : X → C)
    (hsurj : Function.Surjective f)
    (hf : ∀ x y, f x = f y ↔ ∃ w : W, w • x = y)
    (σ : X → X) (hσ : ∀ x, f (σ x) = f x)
    (hfin : ∀ w : W, Finite {x : X // σ x = w • x}) :
    (∑ w : W, Nat.card {x : X // σ x = w • x}) = Nat.card C * Nat.card W := by
  have horbit : ∀ x, ∃ w : W, σ x = w • x := by
    intro x
    obtain ⟨w, hw⟩ := (hf x (σ x)).mp (hσ x).symm
    exact ⟨w, hw.symm⟩
  rw [sum_card_twisted σ horbit hfin,
    Nat.card_congr (orbitEquivParameters f hsurj hf)]


/-- Stable parameters are finite when all twisted kernels are finite, and
count with at least one full copy of the acting group per parameter. -/
theorem finite_and_card_mul_le [Fintype W] (f : X → C)
    (hf : ∀ x y, f x = f y ↔ ∃ w : W, w • x = y)
    (σ : X → X) (τ : C → C) (hστ : ∀ x, f (σ x) = τ (f x))
    (c : Set C) (himage : c ⊆ Set.range f)
    (hfixed : ∀ z ∈ c, τ z = z)
    (hfin : ∀ w : W, Finite {x : X // σ x = w • x}) :
    Finite c ∧ Nat.card c * Nat.card W ≤
      ∑ w : W, Nat.card {x : X // σ x = w • x} := by
  let Y : SubMulAction W X :=
    { carrier := f ⁻¹' c
      smul_mem' := by
        intro w x hx
        change f (w • x) ∈ c
        rw [((hf x (w • x)).mpr ⟨w, rfl⟩).symm]
        exact hx }
  let p : Y → c := fun x => ⟨f x, x.property⟩
  have hp : Function.Surjective p := by
    intro z
    obtain ⟨x, hx⟩ := himage z.property
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change f x ∈ c
    rw [hx]
    exact z.property
  have hpeq : ∀ x y : Y, p x = p y ↔ ∃ w : W, w • x = y := by
    intro x y
    constructor
    · intro h
      obtain ⟨w, hw⟩ := (hf x y).mp (congrArg Subtype.val h)
      exact ⟨w, Subtype.ext hw⟩
    · rintro ⟨w, rfl⟩
      apply Subtype.ext
      exact (hf x (w • (x : X))).mpr ⟨w, rfl⟩
  let σY : Y → Y := fun x => ⟨σ x, by
    change f (σ x) ∈ c
    rw [hστ, hfixed _ x.property]
    exact x.property⟩
  have hσY : ∀ x, p (σY x) = p x := by
    intro x
    apply Subtype.ext
    exact (hστ x).trans (hfixed _ x.property)
  let embed (w : W) : {x : Y // σY x = w • x} → {x : X // σ x = w • x} :=
    fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
  have hembed (w : W) : Function.Injective (embed w) := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {x : X // σ x = w • x} => z.val) h
  have hfinY (w : W) : Finite {x : Y // σY x = w • x} := by
    let := hfin w
    exact Finite.of_injective (embed w) (hembed w)
  refine ⟨finite_parameters p hp hpeq σY hσY hfinY, ?_⟩
  rw [← sum_card_twisted_eq p hp hpeq σY hσY hfinY]
  apply Finset.sum_le_sum
  intro w _
  let := hfin w
  exact Nat.card_le_card_of_injective (embed w) (hembed w)

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount.TwistedCount
