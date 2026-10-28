module
public import CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.NativeInner
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.WholeCodeCoordinates

/-!
# The native hexad point and its irreducible interval

The actual source hexad vector spans the native fixed line. The irreducible
inner A6 quotient then excludes any invariant subspace strictly between this
line and the native five-dimensional commutator. These statements retain the
whole-code coordinates used by the original point-row transport.

Source: Aschbacher--Smith H.16.4 and 8.2.11--12, printed pp.403,722.
-/

@[expose] public noncomputable section
open Sporadic.Mathieu MathieuCode MathieuCode.Hexad
open MathieuCode.Hexad.ChiefFlag MathieuCode.Hexad.ChiefFlag.Actions
open Representation Representation.BinaryOffender
open M22ChapterH.Hexad.Action
namespace CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.NativeCoordinates

/-- The native fixed line is spanned by the actual source hexad vector. -/
theorem fixedLine_span : V1.toSubmodule =
    Submodule.span (ZMod 2) {m22HexadVector m22Hexad24Ten_mem} := by
  apply eq_span_singleton_of_mem_of_finrank_eq_one NativeSource.code_clauses.1.dimensions.1
  · rw [← NativeInner.kernel_fixed, ← M22HexadCoordinates.base_kernel]
    exact m22HexadVector_fixed m22Hexad24Ten_mem
  · exact m22HexadVector_ne_zero m22Hexad24Ten_mem

/-- The literal source fixed line and commutator form an irreducible interval
under the inner hexad action. -/
theorem invariant_interval (S : Submodule (ZMod 2) M22Code)
    (h1 : V1.toSubmodule ≤ S) (h5 : S ≤ V5.toSubmodule)
    (hS : ∀ g : M22ChapterH.Hexad.Action.Inner, ∀ v ∈ S,
      m22CodeRepresentation g.val v ∈ S) :
    S = V1.toSubmodule ∨ S = V5.toSubmodule := by
  let ρ := V5.toRepresentation.comp innerToOuter
  let σ := codeCenter.quotientRepresentation.comp innerToOuter
  let P : Subrepresentation ρ := {
    toSubmodule := S.comap V5.toSubmodule.subtype
    apply_mem_toSubmodule g v hv := hS g v hv }
  have hker : codeCenter.toSubmodule.mkQ.ker ≤ P.toSubmodule := by
    rw [Submodule.ker_mkQ]
    exact fun _ hv => h1 hv
  rcases eq_ker_or_top ρ σ codeCenter.toSubmodule.mkQ
    (fun _ _ => rfl) NativeInner.naturalFour_irreducible P hker with he | he
  · left
    apply le_antisymm _ h1
    intro v hv
    have hm : (⟨v,h5 hv⟩ : V5.toSubmodule) ∈ P.toSubmodule := hv
    rw [he, Submodule.ker_mkQ] at hm
    exact hm
  · right
    apply le_antisymm h5
    intro v hv
    have hm : (⟨v,hv⟩ : V5.toSubmodule) ∈ P.toSubmodule := by
      rw [he]; trivial
    exact hm

end CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.NativeCoordinates
