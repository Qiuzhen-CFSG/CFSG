module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation.KernelControl
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.SupportSeparation.TensorSimplicity

/-!
# Comparison with the proper adjacent mixed tensor

Every irreducible binary SL₄ representation with a nonzero {0,1}-highest
vector embeds in the literal natural–exterior mixed tensor. Kernel control
makes the residual kernel of the universal presentation fixed. Its evaluation
in the irreducible target vanishes because an active root moves the highest
vector. Evaluation therefore descends to the tensor orbit, whose proved
simplicity makes the descended nonzero map invertible.

This combines the two independent concrete calculations without identifying
the universal relation quotient with the tensor orbit. It requires neither
faithfulness, absolute irreducibility, a degree bound, nor a module catalogue.
`SupportSeparation` applies the comparison to exclude the reversed support
and to place elementary full-normalizer actors in the component image.

Source application: Aschbacher–Smith K.3.2, printed pp.451,454–455;
Guralnick–Malle, Classification of 2F-modules II, author manuscript,
Proposition 4.8(3), pp.27–28. This finite-group argument supplies the proper
support distinction used by the source's graph-automorphism argument.
-/

public section

open Representation
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.SupportSeparation

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A nonzero proper highest vector in an irreducible binary SL₄ module gives
a nonzero intertwiner into the actual natural–exterior tensor. -/
theorem mixedTensor_comparison
    (σ : Representation (ZMod 2) Group V) (hi : IsIrreducible σ)
    {v : V} (hv : v ≠ 0) (h : LocalHighestVector σ {0, 1} v) :
    ∃ f : IntertwiningMap σ mixedTensor, f ≠ 0 :=
  mixedTensor_comparison_of_kernel_displacements
    kernel_displacements tensorOrbit_isIrreducible σ hi hv h

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.SupportSeparation
