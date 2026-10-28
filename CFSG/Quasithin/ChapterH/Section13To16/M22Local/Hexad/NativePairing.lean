module
public import CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.NativeCoordinates
public import Theory.Representation.BinaryTransvectionGroups.LineCharacters

/-!
# The full native M22 point transvection pairing

The source hexad vector is the actual center of the native five-space.
The full code-core action is its entire transvection radical, so the
coefficient of each displacement identifies the kernel with the full dual
of the literal central quotient. Both the quotient and the point are kept
in their whole-code coordinates.

Source: Aschbacher--Smith H.16.4(2) and 8.2.11--12, pp.403,722.
-/

@[expose] public noncomputable section
open Sporadic.Mathieu MathieuCode MathieuCode.Hexad
open MathieuCode.Hexad.ChiefFlag MathieuCode.Hexad.ChiefFlag.Actions
open Representation Representation.BinaryOffender BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.NativePairing
set_option backward.isDefEq.respectTransparency false

private theorem line_le_five : V1.toSubmodule ≤ V5.toSubmodule :=
  NativeSource.code_clauses.1.strict.2.1.le

/-- The actual source point inside its actual commutator five-space. -/
def point : V5.toSubmodule := ⟨m22HexadVector m22Hexad24Ten_mem,
  by
    apply line_le_five
    rw [NativeCoordinates.fixedLine_span]
    exact Submodule.mem_span_singleton_self _⟩

theorem point_ne_zero : point ≠ 0 := fun h =>
  m22HexadVector_ne_zero m22Hexad24Ten_mem (congrArg Subtype.val h)

theorem center_eq_span : codeCenter.toSubmodule = centerLine point := by
  apply Submodule.map_injective_of_injective V5.toSubmodule.injective_subtype
  change (V1.toSubmodule.comap V5.toSubmodule.subtype).map V5.toSubmodule.subtype = _
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr line_le_five]
  rw [centerLine, Submodule.map_span, Set.image_singleton]
  exact NativeCoordinates.fixedLine_span

/-- The literal central quotient of the native five-space. -/
abbrev Section := V5.toSubmodule ⧸ centerLine point

private theorem kernel_range : codeKernelAction.range = BinaryLinear.radical (centerLine point) :=
  NativeSource.code_clauses.1.full.trans (congrArg BinaryLinear.radical center_eq_span)

/-- The native full core action with its actual radical codomain. -/
def radicalAction : Kernel →* BinaryLinear.radical (centerLine point) :=
  codeKernelAction.codRestrict _ (fun k => by
    rw [← kernel_range]
    exact ⟨k,rfl⟩)

theorem radicalAction_surjective : Function.Surjective radicalAction := by
  intro t
  have ht : t.val ∈ codeKernelAction.range := by
    rw [kernel_range]
    exact t.property
  obtain ⟨k,hk⟩ := ht
  exact ⟨k,Subtype.ext hk⟩

/-- The actual native kernel is the full dual of the actual central quotient. -/
def characterMap : Kernel →* Multiplicative (Module.Dual (ZMod 2) Section) :=
  (lineCharacterHom point point_ne_zero).comp radicalAction

theorem characterMap_surjective : Function.Surjective characterMap :=
  (lineCharacterHom_surjective point point_ne_zero).comp radicalAction_surjective

theorem characterMap_injective : Function.Injective characterMap := by
  intro a b hab
  have he := lineCharacterHom_injective point point_ne_zero hab
  exact NativeSource.code_clauses.1.faithful (congrArg Subtype.val he)

/-- The pairing evaluates the literal native displacement along the original point. -/
theorem characterMap_displacement (k : Kernel) (v : V5.toSubmodule) :
    ((characterMap k).toAdd ((centerLine point).mkQ v)) • point =
      codeKernelAction k v - v :=
  lineCharacter_smul point point_ne_zero (radicalAction k) v

end CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.NativePairing
