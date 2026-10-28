module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Recognition.Seed
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Incident flags for the binary SL₄ trace kernel

A nonzero point and covector with zero pairing define a rank-one trace-zero
endomorphism. The action uses the original natural matrix representation and
its inverse on covectors, so realization intertwines literal conjugation.
Point and covector additivity give relations in the free flag module.

These exposed definitions are shared by two independent proofs: the additive
presentation of the trace kernel and the highest-vector orbit calculation.
Neither relation completeness nor highest-vector recognition is asserted here.

Source: Aschbacher–Smith, K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Lemma 4.5 step 2 and Proposition 4.8 step 3A.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Representation
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Cyclic

/-- A nonzero vector and nonzero covector incident under the ordinary pairing. -/
def Flag := {p : Natural × Natural // p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ dotProduct p.2 p.1 = 0}

instance : Fintype Flag :=
  inferInstanceAs (Fintype {p : Natural × Natural //
    p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ dotProduct p.2 p.1 = 0})
instance : DecidableEq Flag := inferInstanceAs (DecidableEq (Subtype _))

def point (a : Flag) : Natural := a.val.1
def covector (a : Flag) : Natural := a.val.2
def form (y : Natural) : Module.Dual (ZMod 2) Natural := dotProductEquiv (ZMod 2) (Fin 4) y

@[simp] theorem form_apply (y x : Natural) : form y x = dotProduct y x := rfl
@[simp] theorem form_add (x y : Natural) : form (x + y) = form x + form y :=
  (dotProductEquiv (ZMod 2) (Fin 4)).map_add x y

@[ext] theorem Flag.ext {a b : Flag} (hp : point a = point b)
    (hc : covector a = covector b) : a = b := Subtype.ext (Prod.ext hp hc)

/-- The rank-one nilpotent endomorphism belonging to an incident flag. -/
def rankOne (a : Flag) : TraceZero :=
  ⟨(form (covector a)).smulRight (point a), by
    simpa [form_apply, point, covector] using a.property.2.2⟩

/-- The flag defining E₀₃. -/
def seed : Flag := ⟨(Pi.single 0 1, Pi.single 3 1), by decide⟩

@[simp] theorem rankOne_seed : rankOne seed = highestRoot := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  simp only [rankOne, LinearMap.smulRight_apply, highestRoot, form_apply,
    point, covector, seed, LinearMap.proj_apply]
  simp [dotProduct, Pi.single_apply]

private theorem natural_inv (g : Group) (x : Natural) : natural g⁻¹ (natural g x) = x := by
  change (natural g⁻¹ * natural g) x = x
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

/-- Covectors transform by the inverse of the original, marked natural action. -/
def dualTranslate (g : Group) (y : Natural) : Natural :=
  (dotProductEquiv (ZMod 2) (Fin 4)).symm ((form y).comp (natural g⁻¹))

@[simp] theorem form_dualTranslate (g : Group) (y : Natural) :
    form (dualTranslate g y) = (form y).comp (natural g⁻¹) :=
  (dotProductEquiv (ZMod 2) (Fin 4)).apply_symm_apply _

/-- The actual SL₄ action on incident flags. -/
def translate (g : Group) (a : Flag) : Flag :=
  ⟨(natural g (point a), dualTranslate g (covector a)), by
    refine ⟨?_, ?_, ?_⟩
    · intro hz
      have hh := congrArg (natural g⁻¹) hz
      rw [natural_inv, map_zero] at hh
      exact a.property.1 hh
    · intro hz
      have hh := congrArg form hz
      have he : (form (covector a)).comp (natural g⁻¹) = 0 := by
        rw [form_dualTranslate] at hh
        simpa only [show form 0 = 0 from map_zero (dotProductEquiv (ZMod 2) (Fin 4))] using hh
      have hf : form (covector a) = 0 := by
        apply LinearMap.ext
        intro x
        have hh := LinearMap.congr_fun he (natural g x)
        simpa only [LinearMap.comp_apply, natural_inv, LinearMap.zero_apply] using hh
      apply a.property.2.1
      change covector a = 0
      exact (dotProductEquiv (ZMod 2) (Fin 4)).injective (by
        simpa only [form, map_zero] using hf)
    · change form (dualTranslate g (covector a)) (natural g (point a)) = 0
      rw [form_dualTranslate, LinearMap.comp_apply, natural_inv]
      exact a.property.2.2⟩

@[simp] theorem point_translate (g : Group) (a : Flag) :
    point (translate g a) = natural g (point a) := rfl

@[simp] theorem covector_translate (g : Group) (a : Flag) :
    covector (translate g a) = dualTranslate g (covector a) := rfl

@[simp] theorem translate_one (a : Flag) : translate 1 a = a := by
  apply Flag.ext
  · change natural 1 (point a) = point a
    rw [map_one]
    rfl
  · apply (dotProductEquiv (ZMod 2) (Fin 4)).injective
    change form (dualTranslate 1 (covector a)) = form (covector a)
    rw [form_dualTranslate, inv_one, map_one]
    rfl

theorem translate_mul (g h : Group) (a : Flag) :
    translate (g * h) a = translate g (translate h a) := by
  apply Flag.ext
  · change natural (g * h) (point a) = natural g (natural h (point a))
    rw [map_mul]
    rfl
  · apply (dotProductEquiv (ZMod 2) (Fin 4)).injective
    change form (dualTranslate (g * h) (covector a)) =
      form (dualTranslate g (dualTranslate h (covector a)))
    rw [form_dualTranslate, form_dualTranslate, form_dualTranslate, mul_inv_rev, map_mul,
      Module.End.mul_eq_comp, LinearMap.comp_assoc]

/-- Rank-one realization intertwines the marked flag and trace-kernel actions. -/
theorem rankOne_translate (g : Group) (a : Flag) :
    rankOne (translate g a) = traceAction g (rankOne a) := by
  apply Subtype.ext
  rw [traceAction_apply]
  apply LinearMap.ext
  intro x
  change form (dualTranslate g (covector a)) x • natural g (point a) =
    natural g ((form (covector a) (natural g⁻¹ x)) • point a)
  rw [form_dualTranslate, LinearMap.comp_apply, map_smul]

/-- The two elementary additive relations at a flag. -/
def AdditiveTriple (a b c : Flag) : Prop :=
  (covector b = covector a ∧ covector c = covector a ∧ point c = point a + point b) ∨
  (point b = point a ∧ point c = point a ∧ covector c = covector a + covector b)

/-- Either elementary relation is a literal rank-one matrix identity. -/
theorem rankOne_add {a b c : Flag} (h : AdditiveTriple a b c) :
    rankOne a + rankOne b = rankOne c := by
  apply Subtype.ext
  change (form (covector a)).smulRight (point a) +
    (form (covector b)).smulRight (point b) = (form (covector c)).smulRight (point c)
  rcases h with ⟨hb, hc, hx⟩ | ⟨hb, hc, hy⟩
  · rw [hb, hc, hx]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.add_apply, LinearMap.smulRight_apply, smul_add]
  · rw [hb, hc, hy, form_add]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.add_apply, LinearMap.smulRight_apply, add_smul]

abbrev FreeFlags := Flag →₀ ZMod 2

/-- Evaluation of formal flags in the literal trace-zero space. -/
def realization : FreeFlags →ₗ[ZMod 2] TraceZero := Finsupp.linearCombination (ZMod 2) rankOne

/-- A three-term relation written in the free module. -/
def relation (a b c : Flag) : FreeFlags :=
  Finsupp.single a 1 + Finsupp.single b 1 - Finsupp.single c 1

/-- The subspace generated by point and covector additivity. -/
def relations : Submodule (ZMod 2) FreeFlags :=
  Submodule.span (ZMod 2) {r | ∃ a b c, AdditiveTriple a b c ∧ r = relation a b c}

@[simp] theorem realization_single (a : Flag) : realization (Finsupp.single a 1) = rankOne a := by
  simp [realization]

/-- The additive presentation maps into the genuine trace kernel. -/
theorem relations_le_ker : relations ≤ LinearMap.ker realization := by
  apply Submodule.span_le.mpr
  rintro r ⟨a, b, c, h, rfl⟩
  change realization (relation a b c) = 0
  simp only [relation, map_sub, map_add, realization_single, rankOne_add h, sub_self]

/-- Formal translation of flags by the same SL₄ element. -/
def freeTranslate (g : Group) : FreeFlags →ₗ[ZMod 2] FreeFlags :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (translate g)

/-- Realization commutes with every original group element, not merely generators. -/
theorem realization_translate (g : Group) (z : FreeFlags) :
    realization (freeTranslate g z) = traceAction g (realization z) := by
  exact LinearMap.congr_fun (Finsupp.lmapDomain_linearCombination (ZMod 2)
    (translate g) (traceAction g) (fun a => (rankOne_translate g a).symm)) z

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Cyclic
