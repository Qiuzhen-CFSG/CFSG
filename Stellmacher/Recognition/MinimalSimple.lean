module

public import Stellmacher.Recognition.MinimalSimpleReduction
public import Stellmacher.Recognition.ConversePSL2Prime
public import Stellmacher.Recognition.ConversePSL2ThreePower
public import Stellmacher.Recognition.ConversePSL2Binary
public import Stellmacher.Recognition.ConversePSL3Three
public import Stellmacher.Recognition.ConverseSuzuki
public import Stellmacher.Recognition.MinimalSimpleConverse
public import Stellmacher.Recognition.MinimalSimpleBinaryParameters
public import Stellmacher.Recognition.MinimalSimpleSuzukiParameters
public import Stellmacher.Recognition.MinimalSimpleFinalTheorem

/-!
# Thompson's minimal-simple classification

This assembly exports `isMinimalSimple_iff_thompsonModel`, the complete
classification by the five actual model families with their exact parameter
restrictions, together with its recognition, parameter, and converse APIs.

This assembly exports the minimal-simple predicate and its elementary
subgroup and isomorphism API, the all-prime N and two-local inputs, the
strongly embedded binary PSL2/Suzuki reduction, and the dihedral odd-PSL2
recognition. The latter excludes A7 by its nonsolvable proper A5 subgroup.
It also exports the complete prime-field PSL2 converse for primes greater
than three congruent to two or three modulo five, the odd-prime three-power
PSL2 converse, and the binary PSL2 converse at prime exponents. All three
use Dickson's subgroup classification.
The PSL3(3) converse uses its checked maximal-subgroup classification and also
transports to the actual ABG recognition models.
The binary branch also exports the prime-exponent necessity and iff.
The Suzuki branch exports prime-exponent necessity via its proper nonsolvable
subfield subgroups and the converse via nonsolvable-subgroup recognition
and exclusion of proper Suzuki subgroups at prime degree.
The combined converse transports all five model results along the catalogue's
isomorphisms: every `ThompsonMinimalSimpleModel` is minimal simple.

The local reduction combines these results with Stellmacher's proved
alternatives. The final theorem completes all global recognition cases and
filters the resulting models using minimal simplicity, retaining the genuine
odd-core alternative throughout recognition.

Source: GLS1 §28, Stellmacher Theorem 2, and the Bender--Suzuki and
Gorenstein--Walter theorems, as documented in the imported proof modules.
-/
