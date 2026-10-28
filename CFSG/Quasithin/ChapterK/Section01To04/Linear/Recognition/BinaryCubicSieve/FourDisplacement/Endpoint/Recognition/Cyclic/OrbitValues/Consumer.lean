module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Recognition.Cyclic.OrbitValues
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Recognition.Cyclic

/-!
# Applying endpoint flag values to the trace-kernel presentation

The highest-vector relations now supply the additive equivariant flag
values required by `exists_traceMap_of_flag_values`, with the exact value at
E₀₃. Only completeness of the flag relations remains explicit. Its independent
producer belongs to the trace-cyclic assembly; no adjoint simplicity or actor
estimate is assumed here.

Source: Aschbacher–Smith, K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Lemma 4.5 step 2 and Proposition 4.8 step 3A.
-/

public section
open Representation
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Cyclic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {σ : Representation (ZMod 2) Group V} {v : V}

/-- Endpoint highest-vector relations construct the normalized trace map,
conditional only on completeness of the elementary flag presentation. -/
theorem exists_traceMap_of_localHighest
    (hker : LinearMap.ker realization ≤ relations)
    (h : LocalHighestVector σ {0, 2} v) :
    ∃ f : IntertwiningMap traceAction σ, f highestRoot = v := by
  obtain ⟨b, hb, he, hs⟩ := exists_flag_values_of_localHighest h
  exact exists_traceMap_of_flag_values hker b hb he hs

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Cyclic
