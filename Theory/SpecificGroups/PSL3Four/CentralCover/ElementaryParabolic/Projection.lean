module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ElementaryParabolic.Lifting
import all Theory.SpecificGroups.PSL3Four.CentralCover.ElementaryParabolic.Lifting

/-! # The original central projection on representatives
This internal proof split gives a stable equation for the opaque projection
of Lifting. Only this specification is public; consumers need no definition
body access. It identifies the actual cover map in the Thompson source
application of I.2.2(3b), Aschbacher--Smith 2.5.7, printed p.555.
-/

public section
open Subgroup
namespace Matrix.PSL3Four.ElementaryParabolic
variable {E:Type*} [Group E]
theorem centerProjection_apply (e:E⧸center E≃*PSL) (x:E) :
    centerProjection e x=e (QuotientGroup.mk' (center E) x) := by
  exact congrArg (fun f:E→*PSL=>f x)
    (show centerProjection e=e.toMonoidHom.comp (QuotientGroup.mk' (center E)) from rfl)
end Matrix.PSL3Four.ElementaryParabolic
