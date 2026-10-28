module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation.Presentation
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation.KernelControl.Quotient
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation.KernelControl.TensorRank
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation.KernelControl.UniversalBound

/-!
# Kernel control for the proper adjacent universal presentation

The literal tensor orbit has at least twenty independent vectors, and the
geometric flag evaluation bounds the universal relation quotient by twenty-one.
Its residual tensor kernel is therefore at most one-dimensional, hence fixed
over the binary field. Every displacement of a vector killed by tensor
evaluation belongs to the original translated relation space.

The comparison application uses the original highest-vector relations and the
literal natural–exterior representation. It discharges kernel control and
retains only the independent tensor-orbit simplicity premise for the comparison
owner. No identification of the universal quotient with the tensor orbit is used.

Source application: Aschbacher–Smith K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Proposition 4.8(3), pp.27–28.
-/

public section

open Representation
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.SupportSeparation

/-- Only the upper bound for the actual universal quotient remains for kernel control. -/
theorem kernel_displacements_of_universal_finrank_le
    (hupper : Module.finrank (ZMod 2) KernelControl.Universal ≤ 21)
    (x : Free) (hx : tensorOrbitMap x = 0) (g : Group) :
    regular g x - x ∈ relations :=
  KernelControl.kernel_displacements_of_dimension_bounds hupper
    KernelControl.tensorOrbit_finrank_ge_twenty x hx g

/-- Every displacement of a vector killed by the literal tensor orbit map is
a translated highest-vector relation, without any dimension or simplicity premise. -/
theorem kernel_displacements
    (x : Free) (hx : tensorOrbitMap x = 0) (g : Group) :
    regular g x - x ∈ relations :=
  kernel_displacements_of_universal_finrank_le
    KernelControl.universal_finrank_le_twenty_one x hx g

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The concrete dimension bound supplies the kernel premise of the comparison theorem. -/
theorem mixedTensor_comparison_of_universal_finrank_le
    (hupper : Module.finrank (ZMod 2) KernelControl.Universal ≤ 21)
    (hsimple : IsIrreducible tensorOrbit.toRepresentation)
    (σ : Representation (ZMod 2) Group V) (hi : IsIrreducible σ)
    {v : V} (hv : v ≠ 0) (h : LocalHighestVector σ {0, 1} v) :
    ∃ f : IntertwiningMap σ mixedTensor, f ≠ 0 :=
  mixedTensor_comparison_of_kernel_displacements
    (kernel_displacements_of_universal_finrank_le hupper) hsimple σ hi hv h

/-- Kernel control is proved for the concrete model. Only simplicity of the
tensor orbit remains as an independent model premise for the comparison owner. -/
theorem mixedTensor_comparison_of_tensorOrbit_irreducible
    (hsimple : IsIrreducible tensorOrbit.toRepresentation)
    (σ : Representation (ZMod 2) Group V) (hi : IsIrreducible σ)
    {v : V} (hv : v ≠ 0) (h : LocalHighestVector σ {0, 1} v) :
    ∃ f : IntertwiningMap σ mixedTensor, f ≠ 0 :=
  mixedTensor_comparison_of_kernel_displacements kernel_displacements hsimple σ hi hv h

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.SupportSeparation
