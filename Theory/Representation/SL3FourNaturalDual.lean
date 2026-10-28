module

public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Theory.Combinatorics.ProjectivePlaneMatrixAction
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Critical binary lines in the natural-plus-dual SL₃(4) module

The coefficient field is the actual four-element field F₂[a]/(a²+a+1).
SL₃ acts on pairs of column vectors by the natural and inverse-transpose
matrices. `dualCoordinateEquiv` identifies the second action with the
F₄-linear dual. All dimensions in the obstruction lemmas are binary.

For a full root group, displacements are F₄ scalar multiples. A binary line
cannot contain a nonzero vector and all its scalar multiples. Consequently
the common-line condition forces fixed points; the root fixed space has
codimension four. Adding one independent root forces a critical subspace to
have dimension at most seven. The same bound follows for the interchange of
the two six-dimensional binary summands from its difference projection.
These yield the root, root-plane, and graph-swap obstructions; no assertion
that arbitrary actors possess those markings is made here.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
13.8.20, printed p.955, using the common-center conditions of F.9.13(6)
and F.9.16(2). The implementation reuses this project's four-element field
and Mathlib matrix actions; no ATLAS code is copied.
-/

@[expose] public section
noncomputable section
namespace Representation.SL3FourNaturalDual
open Matrix
abbrev F := SL2FourNatural.F
abbrev W := Fin 3 → F
abbrev V := W × W
abbrev SL := Matrix.SpecialLinearGroup (Fin 3) F

def natural : Representation (ZMod 2) SL W where
  toFun g := (specialLinearNatural 3 g).restrictScalars (ZMod 2)
  map_one' := by
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun (specialLinearNatural 3).map_one v
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun ((specialLinearNatural 3).map_mul g h) v

def dualCoordinates : Representation (ZMod 2) SL W :=
  natural.comp SpecialLinearGroup.inverseTranspose

def representation : Representation (ZMod 2) SL V := natural.prod dualCoordinates

lemma representation_apply (g : SL) (v : V) :
    representation g v = (g.val.mulVec v.1, (g⁻¹).val.transpose.mulVec v.2) := rfl

/-- The highest-root matrices, with every parameter in the actual four-element field. -/
def root (a : F) : SL := ⟨!![1, 0, a; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

lemma root_mul (a b : F) : root a * root b = root (a+b) := by
  apply Subtype.ext
  change (root a).val * (root b).val = (root (a+b)).val
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [root, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

lemma root_zero : root 0 = 1 := by
  apply Subtype.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simp [root]

lemma root_inv (a : F) : (root a)⁻¹ = root a := by
  apply inv_eq_of_mul_eq_one_left
  rw [root_mul, CharTwo.add_self_eq_zero, root_zero]

lemma root_action (a : F) (v : V) : representation (root a) v =
    (![v.1 0 + a * v.1 2, v.1 1, v.1 2],
     ![v.2 0, v.2 1, v.2 2 + a * v.2 0]) := by
  rw [representation_apply, root_inv]
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [root, Matrix.mulVec, dotProduct, Fin.sum_univ_three, add_comm]

lemma root_displacement (a : F) (v : V) : representation (root a) v - v =
    (![a * v.1 2, 0, 0], ![0, 0, a * v.2 0]) := by
  rw [root_action]
  apply Prod.ext <;> funext i <;> fin_cases i <;> simp

lemma root_displacement_smul (a : F) (v : V) :
    representation (root a) v - v = a • (representation (root 1) v - v) := by
  simp only [root_displacement, one_mul]
  apply Prod.ext <;> funext i <;> fin_cases i <;> simp

lemma root_injective : Function.Injective root := by
  intro a b h
  exact congrArg (fun g : SL => g 0 2) h

lemma root_one_ne_one : root 1 ≠ 1 := by
  rw [← root_zero]
  exact fun h => one_ne_zero (root_injective h)

/-- A scalar outside the binary prime field. -/
def omega : F := ⟨0, 1⟩
lemma omega_ne_zero : omega ≠ 0 := by decide +kernel
lemma omega_ne_one : omega ≠ 1 := by decide +kernel

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

lemma mem_binary_line (s x : U) : x ∈ Submodule.span (ZMod 2) {s} ↔ x = 0 ∨ x = s := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    fin_cases a
    · change (0 : ZMod 2) • s = 0 ∨ (0 : ZMod 2) • s = s
      simp
    · change (1 : ZMod 2) • s = 0 ∨ (1 : ZMod 2) • s = s
      simp
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩

variable [Module F U]

/-- A binary line contains no nonzero vector together with its F₄ scalar multiples. -/
lemma eq_zero_of_scalar_multiples_in_binary_line (s x : U)
    (h : ∀ a : F, a • x ∈ Submodule.span (ZMod 2) {s}) : x = 0 := by
  have hx := (mem_binary_line s x).mp (by simpa using h 1)
  rcases hx with hx | hx
  · exact hx
  by_contra hn
  have hw := (mem_binary_line s (omega • x)).mp (h omega)
  rcases hw with hw | hw
  · exact hn ((smul_eq_zero.mp hw).resolve_left omega_ne_zero)
  · have he : (omega - 1) • x = 0 := by rw [sub_smul, one_smul, hw, hx, sub_self]
    exact hn ((smul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr omega_ne_one))

/-- The full root group cannot act nontrivially with a single binary commutator center. -/
lemma root_fixes_of_common_binary_line (D : Submodule (ZMod 2) V) (s : V)
    (h : ∀ a : F, ∀ d ∈ D, representation (root a) d - d ∈ Submodule.span (ZMod 2) {s}) :
    ∀ a : F, ∀ d ∈ D, representation (root a) d = d := by
  intro a d hd
  have hzero : representation (root 1) d - d = 0 :=
    eq_zero_of_scalar_multiples_in_binary_line s _ (fun b => by
      rw [← root_displacement_smul]
      exact h b d hd)
  apply sub_eq_zero.mp
  rw [root_displacement_smul, hzero, smul_zero]

lemma no_faithful_root_critical_line (D : Submodule (ZMod 2) V) (s : V)
    (hfaith : ∀ a : F, (∀ d ∈ D, representation (root a) d = d) → root a = 1) :
    ¬ ∀ a : F, ∀ d ∈ D, representation (root a) d - d ∈ Submodule.span (ZMod 2) {s} := by
  intro h
  exact root_one_ne_one (hfaith 1 (root_fixes_of_common_binary_line D s h 1))

lemma finrank_field : Module.finrank (ZMod 2) F = 2 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
  rw [Nat.card_eq_fintype_card, SL2FourNatural.card_field,
    Nat.card_eq_fintype_card, ZMod.card] at h
  exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
    (show (2 : ℕ)^2 = 2 ^ Module.finrank (ZMod 2) F from h)).symm

/-- Covectors are the genuine F₄-linear dual, with the binary scalar structure retained. -/
def dualCoordinateEquiv : W ≃ₗ[ZMod 2] Module.Dual F W :=
  (dotProductEquiv F (Fin 3)).restrictScalars (ZMod 2)

lemma dualCoordinateEquiv_equivariant (g : SL) (w : W) :
    dualCoordinateEquiv (dualCoordinates g w) =
      (specialLinearNatural 3).dual g (dualCoordinateEquiv w) := by
  apply LinearMap.ext
  intro v
  change ((g⁻¹).val.transpose.mulVec w) ⬝ᵥ v = w ⬝ᵥ ((g⁻¹).val.mulVec v)
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]

lemma finrank_space : Module.finrank (ZMod 2) V = 12 := by
  simp [V, W, Module.finrank_prod, Module.finrank_pi_fintype, finrank_field]

/-- The two coordinates detected by the full highest-root group. -/
def rootProjection : V →ₗ[ZMod 2] F × F where
  toFun v := (v.1 2, v.2 0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rootFixed : Submodule (ZMod 2) V := LinearMap.ker rootProjection

lemma rootProjection_surjective : Function.Surjective rootProjection := by
  rintro ⟨a,b⟩
  exact ⟨(![0,0,a], ![b,0,0]), rfl⟩

lemma mem_rootFixed (v : V) : v ∈ rootFixed ↔ ∀ a : F, representation (root a) v = v := by
  change (rootProjection v = 0) ↔ _
  constructor
  · intro h a
    have hx : v.1 2 = 0 := congrArg Prod.fst h
    have hy : v.2 0 = 0 := congrArg Prod.snd h
    apply sub_eq_zero.mp
    rw [root_displacement, hx, hy]
    apply Prod.ext <;> funext i <;> fin_cases i <;> simp
  · intro h
    have he := sub_eq_zero.mpr (h 1)
    rw [root_displacement] at he
    apply Prod.ext
    · change v.1 2 = 0
      simpa using congrArg (fun w : V => w.1 0) he
    · change v.2 0 = 0
      simpa using congrArg (fun w : V => w.2 2) he

lemma root_fixedCodim : Module.finrank (ZMod 2) (V ⧸ rootFixed) = 4 := by
  have h := (rootProjection.quotKerEquivOfSurjective rootProjection_surjective).finrank_eq
  calc
    Module.finrank (ZMod 2) (V ⧸ rootFixed) =
        Module.finrank (ZMod 2) (F × F) := h
    _ = 4 := by rw [Module.finrank_prod, finrank_field]

/-- Even without faithfulness, a codimension-two subspace cannot have the required center. -/
lemma no_root_critical_line_of_corank_two (D : Submodule (ZMod 2) V) (s : V)
    (hD : Module.finrank (ZMod 2) (V ⧸ D) ≤ 2) :
    ¬ ∀ a : F, ∀ d ∈ D, representation (root a) d - d ∈ Submodule.span (ZMod 2) {s} := by
  intro h
  have hle : D ≤ rootFixed := by
    intro d hd
    exact (mem_rootFixed d).mpr (fun a => root_fixes_of_common_binary_line D s h a d hd)
  have hdim := Submodule.finrank_mono hle
  have h₁ := D.finrank_quotient_add_finrank
  have h₂ := rootFixed.finrank_quotient_add_finrank
  rw [root_fixedCodim] at h₂
  omega

/-- The independent root at position (0,1). -/
def secondRoot (a : F) : SL :=
  ⟨!![1, a, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

lemma secondRoot_inv (a : F) : (secondRoot a)⁻¹ = secondRoot a := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change (secondRoot a).val * (secondRoot a).val = 1
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [secondRoot, Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

lemma secondRoot_displacement (a : F) (v : V) :
    representation (secondRoot a) v - v =
      (![a * v.1 1, 0, 0], ![0, a * v.2 0, 0]) := by
  rw [representation_apply, secondRoot_inv]
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [secondRoot, Matrix.mulVec, dotProduct, Fin.sum_univ_three, add_sub_cancel_left]

lemma finrank_natural : Module.finrank (ZMod 2) W = 6 := by
  simp [W, Module.finrank_pi_fintype, finrank_field]

/-- Coordinates moved by the root plane with common center F₄ e₀. -/
def planeProjection : V →ₗ[ZMod 2] W where
  toFun v := ![v.1 1, v.1 2, v.2 0]
  map_add' _ _ := by funext i; fin_cases i <;> rfl
  map_smul' _ _ := by funext i; fin_cases i <;> rfl

lemma planeProjection_surjective : Function.Surjective planeProjection := by
  intro w
  refine ⟨(![0,w 0,w 1], ![w 2,0,0]), ?_⟩
  funext i
  fin_cases i <;> rfl

private lemma finrank_of_image_in_line {P : Type*} [AddCommGroup P] [Module (ZMod 2) P]
    [FiniteDimensional (ZMod 2) P]
    (f : V →ₗ[ZMod 2] P) (D : Submodule (ZMod 2) V) (s : P)
    (h : ∀ d ∈ D, f d ∈ Submodule.span (ZMod 2) {s}) :
    Module.finrank (ZMod 2) D ≤ Module.finrank (ZMod 2) (LinearMap.ker f) + 1 := by
  let fD := f.comp D.subtype
  have hr : LinearMap.range fD ≤ Submodule.span (ZMod 2) {s} := by
    rintro _ ⟨d, rfl⟩
    exact h d d.property
  have hk : (LinearMap.ker fD).map D.subtype ≤ LinearMap.ker f := by
    rintro _ ⟨d, hd, rfl⟩
    exact hd
  have hkd := (Submodule.equivMapOfInjective D.subtype D.subtype_injective
    (LinearMap.ker fD)).finrank_eq
  have hkdim := Submodule.finrank_mono hk
  have hrdim := Submodule.finrank_mono hr
  have hline : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {s}) ≤ 1 := by
    by_cases hs : s = 0
    · rw [hs, Submodule.span_zero_singleton, finrank_bot]
      omega
    · rw [finrank_span_singleton hs]
  have htotal := fD.finrank_range_add_finrank_ker
  omega

/-- A full root and one independent root already forbid a critical binary
line on a subspace of corank at most four. -/
lemma no_root_plane_critical_line (D : Submodule (ZMod 2) V) (s : V)
    (hD : Module.finrank (ZMod 2) (V ⧸ D) ≤ 4)
    (hroot : ∀ a : F, ∀ d ∈ D,
      representation (root a) d - d ∈ Submodule.span (ZMod 2) {s})
    (hsecond : ∀ d ∈ D,
      representation (secondRoot 1) d - d ∈ Submodule.span (ZMod 2) {s}) : False := by
  have hfix := root_fixes_of_common_binary_line D s hroot
  have hcoords (d : V) (hd : d ∈ D) : d.1 2 = 0 ∧ d.2 0 = 0 := by
    have he := sub_eq_zero.mpr (hfix 1 d hd)
    rw [root_displacement] at he
    exact ⟨by simpa using congrArg (fun w : V => w.1 0) he,
      by simpa using congrArg (fun w : V => w.2 2) he⟩
  have himage : ∀ d ∈ D, planeProjection d ∈
      Submodule.span (ZMod 2) {(![s.1 0,0,0] : W)} := by
    intro d hd
    obtain ⟨hx, hy⟩ := hcoords d hd
    rcases (mem_binary_line s _).mp (hsecond d hd) with he | he
    · apply (mem_binary_line _ _).mpr
      left
      have hc : d.1 1 = 0 := by
        simpa [secondRoot_displacement] using congrArg (fun w : V => w.1 0) he
      funext i
      fin_cases i <;> simp [planeProjection, hx, hy, hc]
    · apply (mem_binary_line _ _).mpr
      right
      have hc : d.1 1 = s.1 0 := by
        simpa [secondRoot_displacement] using congrArg (fun w : V => w.1 0) he
      funext i
      fin_cases i <;> simp [planeProjection, hx, hy, hc]
  have hdim := finrank_of_image_in_line planeProjection D _ himage
  have hker := planeProjection.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr planeProjection_surjective,
    finrank_top, finrank_natural, finrank_space] at hker
  have hquot := D.finrank_quotient_add_finrank
  rw [finrank_space] at hquot
  omega

/-- The graph involution in natural-plus-dual coordinates. -/
def graphSwap : V ≃ₗ[ZMod 2] V := LinearEquiv.prodComm (ZMod 2) W W

/-- Its fixed-space quotient is measured by the difference of the coordinates. -/
def graphProjection : V →ₗ[ZMod 2] W :=
  LinearMap.snd (ZMod 2) W W - LinearMap.fst (ZMod 2) W W

lemma graphProjection_surjective : Function.Surjective graphProjection := by
  intro w
  exact ⟨(0,w), sub_zero w⟩

/-- A graph involution also forbids the common binary center at corank at most four. -/
lemma no_graph_critical_line (D : Submodule (ZMod 2) V) (s : V)
    (hD : Module.finrank (ZMod 2) (V ⧸ D) ≤ 4)
    (hcomm : ∀ d ∈ D, graphSwap d - d ∈ Submodule.span (ZMod 2) {s}) : False := by
  have himage : ∀ d ∈ D, graphProjection d ∈ Submodule.span (ZMod 2) {s.1} := by
    intro d hd
    rcases (mem_binary_line s _).mp (hcomm d hd) with he | he
    · exact (mem_binary_line _ _).mpr (Or.inl (congrArg Prod.fst he))
    · exact (mem_binary_line _ _).mpr (Or.inr (congrArg Prod.fst he))
  have hdim := finrank_of_image_in_line graphProjection D s.1 himage
  have hker := graphProjection.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr graphProjection_surjective,
    finrank_top, finrank_natural, finrank_space] at hker
  have hquot := D.finrank_quotient_add_finrank
  rw [finrank_space] at hquot
  omega

end Representation.SL3FourNaturalDual
