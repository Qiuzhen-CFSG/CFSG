module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.CubicFixedSpace

/-!
# The natural SL₃(2) fixed-space obstruction

The radical of a line is a two-group whose common fixed space is the line.
An element of order three on the complementary plane normalizes the radical
and fixes that line. The same element fixes the common fixed space on any
number of isomorphic natural copies. The actual binary matrix-to-linear
equivalence transports the calculation to SL₃(2).

Cubic lifting permits a central kernel below this section and a trivial
quotient above it, without splitting either extension. Sylow conjugacy then
gives an element outside any specified ambient Sylow two-subgroup fixing its
fixed space. This is the module calculation used in the C.1.34 alternatives
in Aschbacher–Smith, combined manuscript (1 March 2004), printed pp.136–137
and the proof of 15.4.20, p.1164; it does not assert that any group has such
a section.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.Natural

abbrev Space := Fin 3 → ZMod 2
abbrev Actor := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
abbrev LinearActor := BinaryLinear.GL Space

def cycle : LinearActor where
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
  have := congrArg (fun g : LinearActor => g ![0, 1, 0]) h
  have := congrFun this 1
  change (0 : ZMod 2) = 1 at this
  exact zero_ne_one this

def line : Submodule (ZMod 2) Space := Submodule.span (ZMod 2) {Pi.single 0 1}

theorem line_ne_bot : line ≠ ⊥ := by
  apply mt Submodule.span_singleton_eq_bot.mp
  intro h
  have := congrFun h 0
  norm_num at this

theorem cycle_fixes_line (v : Space) (hv : v ∈ line) : cycle v = v := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul]
  congr 1
  decide +kernel

theorem cycle_normalizes : cycle ∈ normalizer (BinaryLinear.radical line : Set LinearActor) := by
  apply BinaryLinear.parabolic_le_normalizer line
  intro v
  constructor
  · intro hv
    have he := cycle_fixes_line (cycle v) hv
    have hv' : cycle v = v := cycle.injective he
    rwa [hv'] at hv
  · intro hv
    simpa only [cycle_fixes_line v hv] using hv

def linearCopies (a : ℕ) : Representation (ZMod 2) LinearActor (Fin a → Space) where
  toFun g :=
    { toFun v i := g (v i)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_one' := by ext; rfl
  map_mul' := by intros; ext; rfl

noncomputable def copies (a : ℕ) : Representation (ZMod 2) Actor (Fin a → Space) :=
  (linearCopies a).comp (BinaryLinear.OuterCyclic.slEquivLinear 3).toMonoidHom

theorem copies_apply (a : ℕ) (g : Actor) (v : Fin a → Space) (i : Fin a) :
    copies a g v i = specialLinearNatural 3 g (v i) := rfl

theorem cycle_fixes_copies (a : ℕ) :
    ∀ v ∈ fixedSpace (linearCopies a) (BinaryLinear.radical line),
      linearCopies a cycle v = v := by
  intro v hv
  funext i
  apply cycle_fixes_line
  apply (BinaryLinear.mem_iff_fixed_radical line_ne_bot (v i)).mpr
  intro g hg
  exact congrFun (hv ⟨g, hg⟩) i

theorem centralSection_enlargement
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (f : Actor →* D) (hf : Function.Injective f)
    (a : ℕ) (U : Subrepresentation (ρ.comp f))
    (q : U.toSubmodule →ₗ[ZMod 2] (Fin a → Space))
    (hq : ∀ g u, q (U.toRepresentation g u) = copies a g (q u))
    (hker : ∀ g u, q u = 0 → U.toRepresentation g u = u)
    (hquot : ∀ g v, ρ (f g) v - v ∈ U) (S : Sylow 2 D) :
    ∃ c : D, c ∉ S ∧ c ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ c v = v := by
  let e := BinaryLinear.OuterCyclic.slEquivLinear 3
  let f' := f.comp e.symm.toMonoidHom
  let U' : Subrepresentation (ρ.comp f') :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule g v hv := U.apply_mem_toSubmodule (e.symm g) hv }
  apply sylow_fixedSpace_enlargement_of_embedded_cubic ρ f'
    (hf.comp e.symm.injective) (BinaryLinear.radical line)
    (BinaryLinear.radical_two line) cycle cycle_pow cycle_ne_one _ S
  apply cubic_fixedSpace_of_central_section (ρ.comp f') (linearCopies a)
    (BinaryLinear.radical line) cycle cycle_pow cycle_normalizes U' q
  · intro g u
    change q (U.toRepresentation (e.symm g) u) = _
    rw [hq]
    change linearCopies a (e (e.symm g)) (q u) = _
    rw [e.apply_symm_apply]
  · exact fun g u hu => hker (e.symm g) u hu
  · exact fun g v => hquot (e.symm g) v
  · exact cycle_fixes_copies a

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.Natural
