module

public import Theory.Mathieu.M22.Properties.CubicInverters.Enumeration
import all Theory.Mathieu.M22.Properties.CubicInverters.Enumeration

/-!
# The value of a certified Sylow row

This is an intentional internal connection to the existing finite enumeration:
`import all` is needed only to prove the value equation for its unexposed
subtype constructor. Consumers use the equation, not the private body.
The enumeration and its public boundary are unchanged.
-/

namespace Sporadic.Mathieu.M22ConjugateGeneration
open M22CubicInverters

public theorem rowSylow_val (i : Fin 256) : (rowSylow i).val = rowElement i := by rfl

end Sporadic.Mathieu.M22ConjugateGeneration
