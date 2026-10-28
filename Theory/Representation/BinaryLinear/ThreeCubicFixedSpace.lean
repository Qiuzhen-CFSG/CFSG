module
public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Theory.Representation.CubicFixedSpace

/-!
# A cubic fixed-space witness for the binary three-dimensional natural module

The point radical in GL₃(𝔽₂) is an elementary two-group with fixed space the
marked line. A cubic acting on the complementary plane normalizes that radical
and fixes the line pointwise. The same witness works on any number of natural
copies. The existing central-section lifting theorem retains central kernels
and trivial quotients, and Sylow conjugacy works in every finite overgroup.
Source application: Aschbacher–Smith B.5.1(1)(i–ii), C.2.7 and15.4.20.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace BinaryLinear.ThreeFixedSpace

abbrev Space := Fin 3 → ZMod 2
abbrev Actor := BinaryLinear.GL Space

def natural : Representation (ZMod 2) Actor Space where
  toFun g := g.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

def cycle : Actor where
  toFun v := ![v 0, v 2, v 1 + v 2]
  invFun v := ![v 0, v 1 + v 2, v 1]
  map_add' := by decide +kernel
  map_smul' := by decide +kernel
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem cycle_pow : cycle ^ 3 = 1 := by
  apply LinearEquiv.ext
  decide +kernel

theorem cycle_ne_one : cycle ≠ 1 := by
  intro h
  have := congrArg (fun g : Actor => g ![0, 1, 0]) h
  have := congrFun this 1
  change (0 : ZMod 2) = 1 at this
  exact zero_ne_one this

def line : Submodule (ZMod 2) Space := Submodule.span (ZMod 2) {Pi.single 0 1}
theorem line_ne_bot : line ≠ ⊥ := by
  apply mt Submodule.span_singleton_eq_bot.mp
  intro h
  have := congrFun h 0
  norm_num at this

def unipotent : Subgroup Actor := radical line

theorem unipotent_two : IsPGroup 2 unipotent := radical_two line

private theorem cycle_fixes_line (v : Space) (hv : v ∈ line) : cycle v = v := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul]
  congr 1
  decide +kernel

theorem cycle_normalizes : cycle ∈ normalizer (unipotent : Set Actor) := by
  apply parabolic_le_normalizer line
  intro v
  constructor
  · intro hv
    have he := cycle_fixes_line (cycle v) hv
    have hv' : cycle v = v := cycle.injective he
    rwa [hv'] at hv
  · intro hv
    simpa only [cycle_fixes_line v hv] using hv

theorem cycle_fixes_natural :
    ∀ v ∈ Representation.BinaryOffender.fixedSpace natural unipotent, natural cycle v = v := by
  intro v hv
  apply cycle_fixes_line
  apply (mem_iff_fixed_radical line_ne_bot v).mpr
  intro g hg
  exact hv ⟨g,hg⟩


noncomputable def copies (a : ℕ) : Representation (ZMod 2) Actor (Fin a → Space) where
  toFun g :=
    { toFun v := fun i => natural g (v i)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_one' := by ext; simp
  map_mul' := by intros; ext; simp [map_mul, Module.End.mul_apply]

theorem cycle_fixes_copies (a : ℕ) :
    ∀ v ∈ Representation.BinaryOffender.fixedSpace (copies a) unipotent, copies a cycle v = v := by
  intro v hv
  funext i
  apply cycle_fixes_natural
  intro g
  exact congrArg (fun w => w i) (hv g)

/-- An actual natural central section supplies the cubic obstruction in every overgroup. -/
theorem centralSection_enlargement
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (f : Actor →* D) (hf : Function.Injective f)
    (a : ℕ) (U : Subrepresentation (ρ.comp f))
    (q : U.toSubmodule →ₗ[ZMod 2] (Fin a → Space))
    (hq : ∀ g u, q (U.toRepresentation g u) = copies a g (q u))
    (hker : ∀ g u, q u = 0 → U.toRepresentation g u = u)
    (hquot : ∀ g v, ρ (f g) v - v ∈ U) (S : Sylow 2 D) :
    ∃ c : D, c ∉ S ∧ c ^ 3 = 1 ∧
      ∀ v ∈ Representation.BinaryOffender.fixedSpace ρ (S : Subgroup D), ρ c v = v := by
  apply sylow_fixedSpace_enlargement_of_embedded_cubic ρ f hf unipotent
    unipotent_two cycle cycle_pow cycle_ne_one _ S
  exact cubic_fixedSpace_of_central_section (ρ.comp f) (copies a)
    unipotent cycle cycle_pow cycle_normalizes U q hq hker hquot
    (cycle_fixes_copies a)

end BinaryLinear.ThreeFixedSpace
