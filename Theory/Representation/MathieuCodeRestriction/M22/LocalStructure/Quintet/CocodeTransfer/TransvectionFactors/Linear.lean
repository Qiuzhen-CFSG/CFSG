module

public import Theory.Representation.BinaryTransvectionGroups.Basic
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.FieldTheory.Finiteness

/-!
# Linear forms for binary transvection groups

A faithful group of transvections with a common one-dimensional center embeds
linearly in the dual space by its displacement forms. Transposing this embedding
makes the evaluation map onto the dual of the actual additive actor. Its kernel
is the common fixed space, giving the exact fixed-dimension formula.

The separate cardinal bound encodes a radical element by its induced map from
the quotient to the center; it does not assume the image is the full radical.
These are the linear-algebra steps used in Aschbacher--Smith H.15.4, printed p.400.
-/

@[expose] public section
noncomputable section
open scoped IsMulCommutative
open BinaryLinear
namespace BinaryTransvectionGroups.LineAction
variable {V H : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Group H]

def radicalCoordinate (W : Submodule (ZMod 2) V) (g : radical W) :
    (V ⧸ W) →ₗ[ZMod 2] W :=
  W.liftQ ((g.val.toLinearMap - LinearMap.id).codRestrict W g.property.2)
    (by intro x hx; exact Subtype.ext (sub_eq_zero.mpr (g.property.1 x hx)))

theorem radicalCoordinate_injective (W : Submodule (ZMod 2) V) :
    Function.Injective (radicalCoordinate W) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hh := congrArg (fun f : (V ⧸ W) →ₗ[ZMod 2] W => (f (W.mkQ x)).val) he
  change g.val x - x = h.val x - x at hh
  exact sub_left_injective hh

theorem card_radical_le [Finite V] [FiniteDimensional (ZMod 2) V]
    (W : Submodule (ZMod 2) V) :
    Nat.card (radical W) ≤ 2 ^ ((Module.finrank (ZMod 2) V -
      Module.finrank (ZMod 2) W) * Module.finrank (ZMod 2) W) := by
  let : Finite (V ⧸ W) := Finite.of_surjective W.mkQ W.mkQ_surjective
  let : Finite ((V ⧸ W) →ₗ[ZMod 2] W) :=
    Finite.of_injective (fun f : (V ⧸ W) →ₗ[ZMod 2] W => (f : (V ⧸ W) → W))
      DFunLike.coe_injective
  have h := Nat.card_le_card_of_injective _ (radicalCoordinate_injective W)
  rwa [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := (V ⧸ W) →ₗ[ZMod 2] W), Nat.card_zmod,
    Module.finrank_linearMap, Submodule.finrank_quotient] at h

variable (ρ : H →* GL V) (W : Submodule (ZMod 2) V)
  (c : W ≃ₗ[ZMod 2] ZMod 2) (hr : ∀ h, ρ h ∈ radical W)

def form (h : H) : Module.Dual (ZMod 2) V :=
  c.toLinearMap.comp (((ρ h).toLinearMap - LinearMap.id).codRestrict W (hr h).2)

theorem form_eq_zero_iff (h : H) (v : V) : form ρ W c hr h v = 0 ↔ ρ h v = v := by
  change c ⟨ρ h v - v, _⟩ = 0 ↔ _
  rw [map_eq_zero_iff c c.injective]
  exact (Subtype.ext_iff).trans sub_eq_zero

theorem form_mul (a b : H) :
    form ρ W c hr (a * b) = form ρ W c hr a + form ρ W c hr b := by
  ext v
  have hd := (hr a).1 (ρ b v - v) ((hr b).2 v)
  have he : ρ (a * b) v - v = (ρ a v - v) + (ρ b v - v) := by
    rw [map_mul, LinearEquiv.mul_apply]
    rw [map_sub] at hd
    calc
      ρ a (ρ b v) - v = (ρ a (ρ b v) - ρ a v) + (ρ a v - v) := by abel
      _ = _ := by rw [hd]; abel
  change c ⟨ρ (a * b) v - v, _⟩ = c ⟨ρ a v - v, _⟩ + c ⟨ρ b v - v, _⟩
  rw [← map_add]
  apply congrArg c
  exact Subtype.ext he

variable [IsElementaryAbelian 2 H]

def forms : Additive H →ₗ[ZMod 2] Module.Dual (ZMod 2) V :=
  ({ toFun a := form ρ W c hr a.toMul
     map_zero' := by
       ext v
       exact (form_eq_zero_iff ρ W c hr 1 v).mpr (by rw [map_one]; rfl)
     map_add' a b := form_mul ρ W c hr a.toMul b.toMul } :
    Additive H →+ Module.Dual (ZMod 2) V).toZModLinearMap 2

theorem forms_injective (hf : Function.Injective ρ) :
    Function.Injective (forms ρ W c hr) := by
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro a ha
  have hz : forms ρ W c hr a = 0 := ha
  have he : ρ a.toMul = 1 := by
    ext v
    exact (form_eq_zero_iff ρ W c hr a.toMul v).mp
      (LinearMap.congr_fun hz v)
  have : a.toMul = 1 := hf (he.trans (map_one ρ).symm)
  exact this

def evaluation : V →ₗ[ZMod 2] Module.Dual (ZMod 2) (Additive H) :=
  (forms ρ W c hr).flip

theorem evaluation_surjective [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) : Function.Surjective (evaluation ρ W c hr) := by
  have he : evaluation ρ W c hr =
      (forms ρ W c hr).dualMap.comp (Module.evalEquiv (ZMod 2) V).toLinearMap := rfl
  rw [he]
  exact (LinearMap.dualMap_surjective_of_injective
    (forms_injective ρ W c hr hf)).comp (Module.evalEquiv (ZMod 2) V).surjective

theorem evaluation_ker : (evaluation ρ W c hr).ker = BinaryLinear.fixedSpace ρ.range := by
  ext v
  constructor
  · intro hv g hg
    obtain ⟨a, rfl⟩ := hg
    exact (form_eq_zero_iff ρ W c hr a v).mp
      (LinearMap.congr_fun (show evaluation ρ W c hr v = 0 from hv) (Additive.ofMul a))
  · intro hv
    apply LinearMap.ext
    intro a
    exact (form_eq_zero_iff ρ W c hr a.toMul v).mpr (hv _ ⟨a.toMul,rfl⟩)

include c hr in
theorem finrank_fixed_add [FiniteDimensional (ZMod 2) V] [Finite H]
    (hf : Function.Injective ρ) :
    Module.finrank (ZMod 2) (BinaryLinear.fixedSpace ρ.range) +
      Module.finrank (ZMod 2) (Additive H) = Module.finrank (ZMod 2) V := by
  have hd := (evaluation ρ W c hr).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (evaluation_surjective ρ W c hr hf),
    finrank_top, Subspace.dual_finrank_eq, evaluation_ker] at hd
  omega

include c hr in
theorem finrank_fixed_add_of_card [FiniteDimensional (ZMod 2) V] [Finite H]
    (hf : Function.Injective ρ) (r : ℕ) (hcard : Nat.card H = 2 ^ r) :
    Module.finrank (ZMod 2) (BinaryLinear.fixedSpace ρ.range) + r =
      Module.finrank (ZMod 2) V := by
  have hd : Module.finrank (ZMod 2) (Additive H) = r := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive H)
    simpa only [Nat.card_zmod, Nat.card_congr (Additive.toMul : Additive H ≃ H), hcard]
      using hc.symm
  rw [← hd]
  exact finrank_fixed_add ρ W c hr hf

theorem evaluation_ker_of_full (hW : W ≠ ⊥) (hfull : ρ.range = radical W) :
    (evaluation ρ W c hr).ker = W := by
  rw [evaluation_ker, hfull]
  ext v
  exact (BinaryLinear.mem_iff_fixed_radical hW v).symm

/-- The quotient pairing identifies the section with the dual of the actual actor. -/
def quotientDuality [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hW : W ≠ ⊥) (hfull : ρ.range = radical W) :
    (V ⧸ W) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Additive H) :=
  (Submodule.quotEquivOfEq W (evaluation ρ W c hr).ker
    (evaluation_ker_of_full ρ W c hr hW hfull).symm).trans
    ((evaluation ρ W c hr).quotKerEquivOfSurjective
      (evaluation_surjective ρ W c hr hf))

@[simp] theorem quotientDuality_mk [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hW : W ≠ ⊥) (hfull : ρ.range = radical W) (v : V) :
    quotientDuality ρ W c hr hf hW hfull (W.mkQ v) = evaluation ρ W c hr v := rfl

omit [IsElementaryAbelian 2 H] in
/-- A normalizer fixing the center transports displacement forms contragrediently. -/
theorem form_intertwines (s : GL V) (hs : ∀ w ∈ W, s w = w)
    (a b : H) (hab : ρ a * s = s * ρ b) (v : V) :
    form ρ W c hr a (s v) = form ρ W c hr b v := by
  change c ⟨ρ a (s v) - s v, _⟩ = c ⟨ρ b v - v, _⟩
  apply congrArg c
  apply Subtype.ext
  have he := congrArg (fun t : GL V => t v) hab
  change ρ a (s v) = s (ρ b v) at he
  change ρ a (s v) - s v = ρ b v - v
  rw [he, ← map_sub, hs _ ((hr b).2 v)]

end BinaryTransvectionGroups.LineAction
