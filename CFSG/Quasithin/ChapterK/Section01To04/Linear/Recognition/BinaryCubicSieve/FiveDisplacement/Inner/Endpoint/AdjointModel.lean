module

public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.BinaryOffender.Basic
public import Theory.Representation.DualCommutator
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# The literal binary SL₅ adjoint action and its common centralizer

The carrier is the trace kernel in the 5 by 5 matrices over F₂, with action
X ↦ g X g⁻¹. Since the identity has trace one, restriction of trace to every
common matrix centralizer is surjective. Its kernel is exactly the fixed
space in the adjoint module, giving fixedCodim + dim(centralizer) = 25.

For an arbitrary matrix subgroup B, the distinct displacements b − 1 give
distinct maps V/C_V(B) → [V,B]. Counting this vector space bounds log₂|B|
by dim[V,B] times codim C_V(B). These are the two concrete comparisons used
by the common-centralizer bound in AdjointCentralizer.

Source: Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Lemma 4.5 step 2, pp.23–24, using Corollary 2.11(a), pp.9–10.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Adjoint

abbrev Group := Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)
abbrev Natural := Fin 5 → ZMod 2
abbrev Mat := Matrix (Fin 5) (Fin 5) (ZMod 2)
abbrev natural : Representation (ZMod 2) Group Natural := specialLinearNatural 5
abbrev trace : Mat →ₗ[ZMod 2] ZMod 2 := Matrix.traceLinearMap _ _ _

/-- Conjugation on all matrices, before restricting to trace zero. -/
def conjugation : Representation (ZMod 2) Group Mat where
  toFun g :=
    { toFun X := g.val * X * g⁻¹.val
      map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' c X := by simp }
  map_one' := by ext X i j; simp
  map_mul' g h := by
    apply LinearMap.ext
    intro X
    change (g * h).val * X * (g * h)⁻¹.val =
      g.val * (h.val * X * h⁻¹.val) * g⁻¹.val
    simp only [mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc]

@[simp] theorem conjugation_apply (g : Group) (X : Mat) :
    conjugation g X = g.val * X * g⁻¹.val := rfl

theorem trace_conjugation (g : Group) (X : Mat) : trace (conjugation g X) = trace X := by
  change Matrix.trace (g.val * X * g⁻¹.val) = Matrix.trace X
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  have hi : g⁻¹.val * g.val = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [hi, Matrix.one_mul]

/-- The invariant trace kernel. -/
def traceZero : Subrepresentation conjugation where
  toSubmodule := trace.ker
  apply_mem_toSubmodule g X hX := by
    change trace (conjugation g X) = 0
    exact (trace_conjugation g X).trans hX

/-- The actual trace-zero matrix carrier. -/
abbrev Space := trace.ker
/-- The adjoint representation on trace-zero matrices. -/
abbrev action : Representation (ZMod 2) Group Space := traceZero.toRepresentation

@[simp] theorem action_val (g : Group) (X : Space) :
    (action g X).val = g.val * X.val * g⁻¹.val := rfl

@[simp] theorem trace_one : trace (1 : Mat) = 1 := by decide +kernel

theorem finrank_space : Module.finrank (ZMod 2) Space = 24 := by
  have hs : Function.Surjective trace := fun c =>
    ⟨c • 1, by simp only [map_smul, trace_one, smul_eq_mul, mul_one]⟩
  have h := trace.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self] at h
  have hm : Module.finrank (ZMod 2) Mat = 25 := by simp [Mat, Module.finrank_matrix]
  change 1 + Module.finrank (ZMod 2) Space = Module.finrank (ZMod 2) Mat at h
  omega

/-- Matrices commuting with every element of B. -/
def centralizer (B : Subgroup Group) : Submodule (ZMod 2) Mat where
  carrier := {X | ∀ b ∈ B, b.val * X = X * b.val}
  zero_mem' := by simp
  add_mem' hX hY b hb := by simp only [Matrix.mul_add, Matrix.add_mul, hX b hb, hY b hb]
  smul_mem' c X hX b hb := by simp only [Matrix.mul_smul, Matrix.smul_mul, hX b hb]

theorem mem_centralizer_iff (B : Subgroup Group) (X : Mat) :
    X ∈ centralizer B ↔ ∀ b ∈ B, b.val * X = X * b.val := Iff.rfl

theorem conjugation_eq_self_iff (g : Group) (X : Mat) :
    conjugation g X = X ↔ g.val * X = X * g.val := by
  have hi : g⁻¹.val * g.val = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hj : g.val * g⁻¹.val = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  constructor
  · intro h
    have he := congrArg (fun Y : Mat => Y * g.val) h
    simpa only [conjugation_apply, Matrix.mul_assoc, hi, Matrix.mul_one] using he
  · intro h
    change g.val * X * g⁻¹.val = X
    rw [h, Matrix.mul_assoc, hj, Matrix.mul_one]

theorem mem_fixedSpace_iff (B : Subgroup Group) (X : Space) :
    X ∈ fixedSpace action B ↔ X.val ∈ centralizer B := by
  constructor
  · intro h b hb
    have he : action b X = X := h ⟨b, hb⟩
    have hv := congrArg (fun Y : Space => Y.val) he
    rw [action_val] at hv
    exact (conjugation_eq_self_iff b X.val).mp hv
  · intro h b
    exact Subtype.ext ((conjugation_eq_self_iff b X.val).mpr (h b b.property))

private def centralizerTrace (B : Subgroup Group) : centralizer B →ₗ[ZMod 2] ZMod 2 :=
  trace.comp (centralizer B).subtype

private def fixedEquivTraceKernel (B : Subgroup Group) :
    fixedSpace action B ≃ₗ[ZMod 2] (centralizerTrace B).ker where
  toFun X := ⟨⟨X.val.val, (mem_fixedSpace_iff B X.val).mp X.property⟩, X.val.property⟩
  invFun X := ⟨⟨X.val.val, X.property⟩, (mem_fixedSpace_iff B _).mpr X.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_centralizer (B : Subgroup Group) :
    Module.finrank (ZMod 2) (centralizer B) =
      Module.finrank (ZMod 2) (fixedSpace action B) + 1 := by
  have hs : Function.Surjective (centralizerTrace B) := by
    intro c
    refine ⟨⟨c • 1, ?_⟩, ?_⟩
    · intro b _
      simp
    · change trace (c • (1 : Mat)) = c
      simp only [map_smul, trace_one, smul_eq_mul, mul_one]
  have h := (centralizerTrace B).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_self,
    ← (fixedEquivTraceKernel B).finrank_eq] at h
  omega

/-- Removing the fixed scalar line preserves displacement codimension. -/
theorem fixedCodim_add_finrank_centralizer (B : Subgroup Group) :
    fixedCodim action B + Module.finrank (ZMod 2) (centralizer B) = 25 := by
  have h := fixedCodim_add_finrank action B
  rw [finrank_space] at h
  rw [finrank_centralizer]
  omega

abbrev fixedNatural (B : Subgroup Group) := fixedSpace natural B
abbrev movedNatural (B : Subgroup Group) := Coinvariants.ker (natural.comp B.subtype)

private def displacementCoordinate (B : Subgroup Group) (b : B) :
    (Natural ⧸ fixedNatural B) →ₗ[ZMod 2] movedNatural B :=
  (fixedNatural B).liftQ
    ((natural b.val - LinearMap.id).codRestrict (movedNatural B)
      (fun v => Coinvariants.sub_mem_ker (ρ := natural.comp B.subtype) b v))
    (by intro v hv; exact Subtype.ext (sub_eq_zero.mpr (hv b)))

private theorem displacementCoordinate_injective (B : Subgroup Group) :
    Function.Injective (displacementCoordinate B) := by
  intro b c h
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  have he := congrArg
    (fun f : (Natural ⧸ fixedNatural B) →ₗ[ZMod 2] movedNatural B =>
      (f ((fixedNatural B).mkQ v)).val) h
  change natural b.val v - v = natural c.val v - v at he
  exact sub_left_injective he

/-- Counting distinct natural displacements bounds subgroup rank. -/
theorem rank_le_moved_mul_fixedCodim (B : Subgroup Group) :
    rank B ≤ Module.finrank (ZMod 2) (movedNatural B) *
      (5 - Module.finrank (ZMod 2) (fixedNatural B)) := by
  let : Finite ((Natural ⧸ fixedNatural B) →ₗ[ZMod 2] movedNatural B) :=
    Finite.of_injective
      (fun f : (Natural ⧸ fixedNatural B) →ₗ[ZMod 2] movedNatural B =>
        (f : (Natural ⧸ fixedNatural B) → movedNatural B)) DFunLike.coe_injective
  have h := Nat.card_le_card_of_injective _ (displacementCoordinate_injective B)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := (Natural ⧸ fixedNatural B) →ₗ[ZMod 2] movedNatural B), Nat.card_zmod,
    Module.finrank_linearMap, Submodule.finrank_quotient] at h
  have hd : Module.finrank (ZMod 2) Natural = 5 := by simp [Natural]
  rw [hd, mul_comm] at h
  exact (Nat.log_mono_right h).trans_eq (Nat.log_pow (by decide) _)

/-- A commuting matrix gives an endomorphism of the literal restricted action. -/
def centralizerHom (B : Subgroup Group) : centralizer B →ₗ[ZMod 2]
    IntertwiningMap (natural.comp B.subtype) (natural.comp B.subtype) where
  toFun X :=
    { toLinearMap := Matrix.toLin' X.val
      isIntertwining' b := by
        change Matrix.toLin' X.val ∘ₗ Matrix.toLin' b.val.val =
          Matrix.toLin' b.val.val ∘ₗ Matrix.toLin' X.val
        rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul]
        exact congrArg Matrix.toLin' (X.property b.val b.property).symm }
  map_add' _ _ := IntertwiningMap.ext (map_add Matrix.toLin' _ _)
  map_smul' c X := IntertwiningMap.ext (map_smul Matrix.toLin' c X.val)

theorem centralizerHom_injective (B : Subgroup Group) :
    Function.Injective (centralizerHom B) := by
  intro X Y h
  apply Subtype.ext
  exact Matrix.toLin'.injective
    (congrArg (fun f : IntertwiningMap (natural.comp B.subtype) (natural.comp B.subtype) =>
      f.toLinearMap) h)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint.Adjoint
