module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Recognition.Cyclic.FlagRelations
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Recognition.Cyclic

/-!
# Descent from flag values with the presentation premise discharged

The incident-flag presentation supplies the kernel inclusion required by
`exists_traceMap_of_flag_values`. The remaining premises concern only the
independent construction of additive, equivariant flag values and their value
at the highest-root seed. The unconditional cyclic-map assembly retains the
construction of these values.

Source: Aschbacher–Smith, K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Lemma 4.5 step 2 and Proposition 4.8 step 3A.
-/

public noncomputable section
open Representation
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Cyclic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {σ : Representation (ZMod 2) Group V} {v : V}

/-- Additive equivariant flag values give the normalized trace-zero intertwiner;
completeness of the flag relations is now proved, rather than assumed. -/
theorem exists_traceMap_of_additive_flag_values
    (b : Flag → V)
    (hb : ∀ a b' c, AdditiveTriple a b' c → b a + b b' = b c)
    (he : ∀ g a, b (translate g a) = σ g (b a))
    (hs : b seed = v) :
    ∃ f : IntertwiningMap traceAction σ, f highestRoot = v :=
  exists_traceMap_of_flag_values ker_realization_le_relations b hb he hs

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Cyclic
