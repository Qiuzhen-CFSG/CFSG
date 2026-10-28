module

public import Theory.Representation.G2Natural
public import Theory.AtlasPort.LinearGroups.G2.Simplicity

/-!
# Faithfulness of the natural six-dimensional G₂ action

The action is the actual trace-zero octonion quotient by the scalar line.
For fields of order greater than two, simplicity makes its kernel trivial
or the whole group. The short-root element C(1) moves a displayed quotient
vector, excluding the latter possibility. This connects the minimal-degree
centralizer argument to the concrete G₂ model.

Source: the natural G₂ module in Aschbacher--Smith I.1.6(5), printed p.408,
and the local cyclic-Sylow application of I.1.2. Octonion coordinates and
root maps are the licensed ATLAS ports; see LICENSES/ATLAS.txt.
-/

public section

namespace Atlas.G2.MultiplierOrdinary.Nondefining.CyclotomicSylow

open Atlas.SplitOctonion
open Atlas.G2.Explicit

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The trace-zero quotient action is faithful for the ordinary G₂ fields. -/
theorem natural_action_injective (hF : 2 < Nat.card F) :
    Function.Injective (Natural.action F) := by
  let : IsSimpleGroup (Model F) := Atlas.G2.isSimple hF
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases (inferInstance : (Natural.action F).ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hc : rootC (1 : F) ∈ (Natural.action F).ker := by rw [h]; trivial
    let v : Natural.TraceZero F :=
      ⟨basisVector 7, by simp [Natural.mem_traceZero, trace, basisVector]⟩
    have hv := LinearMap.congr_fun (MonoidHom.mem_ker.mp hc) (Natural.mk F v)
    change Natural.action F (rootC 1) (Natural.mk F v) = Natural.mk F v at hv
    rw [Natural.action_mk] at hv
    obtain ⟨a, ha⟩ := (Natural.mk_eq_mk_iff F _ _).mp hv
    have hzero := congrFun ha 0
    simp [v, Natural.traceZeroAction_val, unit, rootC, rootCEquiv, rootCLinear,
      rootCApply, basisVector] at hzero

end Atlas.G2.MultiplierOrdinary.Nondefining.CyclotomicSylow
