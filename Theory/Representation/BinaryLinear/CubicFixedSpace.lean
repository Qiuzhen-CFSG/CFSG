module

public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Theory.Representation.CubicFixedSpace
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Cubic fixed-space witnesses on binary natural and dual modules

Inside GL₄(𝔽₂), the radicals of a line and a containing hyperplane generate
a two-subgroup. An order-three transformation of the two middle coordinates
normalizes this subgroup and fixes its fixed spaces on both the natural
module and its dual. The same witness works on arbitrary numbers of these
modules. Cubic lifting then treats central kernels and trivial quotients,
without requiring either extension to split. Embedding and Sylow conjugacy
produce an element outside every ambient Sylow subgroup fixing its fixed space.

This is the natural/dual calculation used in the binary-linear alternatives
of Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(1)(iii–iv),
(6), printed p.99, and the FF-module exclusion in 15.4.20, printed p.1164.
It is a calculation for the specified modules, not their classification.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace BinaryLinear.FourFixedSpace

abbrev Space := Fin 4 → ZMod 2
abbrev Actor := BinaryLinear.GL Space

def natural : Representation (ZMod 2) Actor Space where
  toFun g := g.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

def cycle : Actor where
  toFun v := ![v 0, v 2, v 1 + v 2, v 3]
  invFun v := ![v 0, v 1 + v 2, v 1, v 3]
  map_add' := by decide +kernel
  map_smul' := by decide +kernel
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem cycle_pow : cycle ^ 3 = 1 := by
  apply LinearEquiv.ext
  decide +kernel

theorem cycle_ne_one : cycle ≠ 1 := by
  intro h
  have := congrArg (fun g : Actor => g ![0, 1, 0, 0]) h
  have := congrFun this 1
  change (0 : ZMod 2) = 1 at this
  exact zero_ne_one this

def line : Submodule (ZMod 2) Space := Submodule.span (ZMod 2) {Pi.single 0 1}
def hyperplane : Submodule (ZMod 2) Space := (LinearMap.proj 3 : Space →ₗ[ZMod 2] ZMod 2).ker

theorem line_le_hyperplane : line ≤ hyperplane := by
  apply Submodule.span_le.mpr
  rintro v (rfl : v = _)
  change (Pi.single 0 1 : Space) 3 = 0
  decide +kernel

theorem line_ne_bot : line ≠ ⊥ := by
  apply mt Submodule.span_singleton_eq_bot.mp
  intro h
  have := congrFun h 0
  norm_num at this

def unipotent : Subgroup Actor := radical line ⊔ radical hyperplane

theorem unipotent_two : IsPGroup 2 unipotent := by
  apply (radical_two line).to_sup_of_normal_left' (radical_two hyperplane)
  apply le_trans _ (parabolic_le_normalizer line)
  intro g hg v
  constructor
  · intro hv
    have he : g v = v := g.injective (hg.1 (g v) (line_le_hyperplane hv))
    rwa [he] at hv
  · intro hv
    simpa only [hg.1 v (line_le_hyperplane hv)] using hv

private theorem cycle_fixes_line (v : Space) (hv : v ∈ line) : cycle v = v := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul]
  congr 1
  decide +kernel

theorem cycle_normalizes : cycle ∈ normalizer (unipotent : Set Actor) := by
  apply normalizer_inf_normalizer_le_normalizer_sup (radical line) (radical hyperplane)
  constructor
  · apply parabolic_le_normalizer line
    intro v
    constructor
    · intro hv
      have he := cycle_fixes_line (cycle v) hv
      have hv' : cycle v = v := cycle.injective he
      rwa [hv'] at hv
    · intro hv
      simpa only [cycle_fixes_line v hv] using hv
  · apply parabolic_le_normalizer hyperplane
    intro v
    rfl

theorem cycle_fixes_natural :
    ∀ v ∈ Representation.BinaryOffender.fixedSpace natural unipotent, natural cycle v = v := by
  intro v hv
  apply cycle_fixes_line
  apply (mem_iff_fixed_radical line_ne_bot v).mpr
  intro g hg
  exact hv ⟨g, mem_sup_left hg⟩

private theorem dual_fixed_vanishes_hyperplane
    (f : Module.Dual (ZMod 2) Space) (hf : f ∈ Representation.BinaryOffender.fixedSpace natural.dual unipotent)
    (w : Space) (hw : w ∈ hyperplane) : f w = 0 := by
  let t := transvection w (LinearMap.proj 3) hw
  have ht : t ∈ radical hyperplane := transvection_mem hw le_rfl
  have h := hf ⟨t⁻¹, mem_sup_right ((radical hyperplane).inv_mem ht)⟩
  have he := congrArg (fun q : Module.Dual (ZMod 2) Space => q (Pi.single 3 1)) h
  change f (t (Pi.single 3 1)) = f (Pi.single 3 1) at he
  have htval : t (Pi.single 3 1) = Pi.single 3 1 + w := by
    simp [t, transvection]
  rw [htval, map_add] at he
  exact add_eq_left.mp he

theorem cycle_fixes_dual :
    ∀ f ∈ Representation.BinaryOffender.fixedSpace natural.dual unipotent, natural.dual cycle f = f := by
  intro f hf
  apply LinearMap.ext
  intro v
  have hw : cycle⁻¹ v - v ∈ hyperplane := by
    change (cycle⁻¹ v - v) 3 = 0
    simp [cycle]
  have hz := dual_fixed_vanishes_hyperplane f hf _ hw
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

noncomputable def copies (a b : ℕ) :
    Representation (ZMod 2) Actor ((Fin a → Space) × (Fin b → Module.Dual (ZMod 2) Space)) where
  toFun g :=
    { toFun v := (fun i => natural g (v.1 i), fun i => natural.dual g (v.2 i))
      map_add' := by intros; ext <;> simp
      map_smul' := by intros; ext <;> simp }
  map_one' := by
    ext <;> simp
    rfl
  map_mul' := by intros; ext <;> simp [map_mul, Module.End.mul_apply]

theorem cycle_fixes_copies (a b : ℕ) :
    ∀ v ∈ Representation.BinaryOffender.fixedSpace (copies a b) unipotent, copies a b cycle v = v := by
  intro v hv
  apply Prod.ext
  · funext i
    apply cycle_fixes_natural
    intro g
    exact congrArg (fun w => w.1 i) (hv g)
  · funext i
    apply cycle_fixes_dual
    intro g
    exact congrArg (fun w => w.2 i) (hv g)

/-- A central section consisting of any numbers of natural and dual copies
has a cubic fixed-space enlargement in every finite overgroup. -/
theorem centralSection_enlargement
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (f : Actor →* D) (hf : Function.Injective f)
    (a b : ℕ) (U : Subrepresentation (ρ.comp f))
    (q : U.toSubmodule →ₗ[ZMod 2]
      ((Fin a → Space) × (Fin b → Module.Dual (ZMod 2) Space)))
    (hq : ∀ g u, q (U.toRepresentation g u) = copies a b g (q u))
    (hker : ∀ g u, q u = 0 → U.toRepresentation g u = u)
    (hquot : ∀ g v, ρ (f g) v - v ∈ U) (S : Sylow 2 D) :
    ∃ c : D, c ∉ S ∧ c ^ 3 = 1 ∧
      ∀ v ∈ Representation.BinaryOffender.fixedSpace ρ (S : Subgroup D), ρ c v = v := by
  apply sylow_fixedSpace_enlargement_of_embedded_cubic ρ f hf unipotent
    unipotent_two cycle cycle_pow cycle_ne_one _ S
  exact cubic_fixedSpace_of_central_section (ρ.comp f) (copies a b)
    unipotent cycle cycle_pow cycle_normalizes U q hq hker hquot
    (cycle_fixes_copies a b)

end BinaryLinear.FourFixedSpace
