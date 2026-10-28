module

public import Theory.SpecificGroups.Janko3.TripleCover.Projection
public import Theory.SpecificGroups.Janko3.Multiplier.Assembly

/-!
# Applying the cubic presentation to the J₃ multiplier assembly

The explicit projection from `TripleCover.Presentation` supplies the triple
cover input of the existing exact-multiplier theorem. Its finite central
kernel calculation uses faithfulness of the original J₃ presentation and a
representation detecting the marked cubic element. Those two concrete inputs,
and the independent upper bound, remain explicit until their owners finish.

Source: Aschbacher--Smith I.1.4(2), printed p.408.
-/

namespace Sporadic.Janko3.TripleCover

open PerfectCentralCovering Theory.GroupTheory

universe u

/-- The lower-bound divisibility for any chosen source universal covering,
without using the independent upper bound. -/
public theorem three_dvd_source_universal_kernel
    [IsQuasisimple Model]
    {U : Type u} [Group U] [Finite U] [IsQuasisimple U]
    (f : Covering U Model) (hf : Covering.IsUniversal.{0, u, 0} f)
    (hinj : Function.Injective
      (RecognitionPresentation.evaluation RecognitionPresentation.model_satisfies))
    (hz : z ≠ 1) : 3 ∣ Nat.card f.toMonoidHom.ker := by
  rw [← Nat.card_congr (schurMultiplierEquivOfUniversal (MulEquiv.refl Model) f hf).toEquiv]
  exact three_dvd_universal_kernel hinj hz

/-- Application to the canonical universal kernel, retaining the independent
upper bound and the two outstanding construction inputs. -/
public theorem universal_kernel_equiv_three_of_bound
    (hinj : Function.Injective
      (RecognitionPresentation.evaluation RecognitionPresentation.model_satisfies))
    (hz : z ≠ 1)
    (hbound : Nat.card (universalProjection Model).ker ≤ 3) :
    Nonempty (PerfectCentralCovering.schurMultiplier Model ≃*
      Multiplicative (ZMod 3)) := by
  let : Finite Presentation := finite_presentation hinj
  exact Multiplier.universal_kernel_equiv_three_of_bound_and_triple_cover hbound
    (cover hinj) (projection_kernel_card hinj hz)

/-- Literal application to the chosen source covering. The map, perfectness,
centrality, finiteness and kernel order of the candidate are all supplied by
the construction, rather than taken as a bundled triple-cover premise. -/
public theorem source_kernel_equiv_three_of_bound
    [IsQuasisimple Model]
    {U : Type u} [Group U] [Finite U] [IsQuasisimple U]
    (f : Covering U Model) (hf : Covering.IsUniversal.{0, u, 0} f)
    (hinj : Function.Injective
      (RecognitionPresentation.evaluation RecognitionPresentation.model_satisfies))
    (hz : z ≠ 1)
    (hbound : Nat.card (universalProjection Model).ker ≤ 3) :
    Nonempty (f.toMonoidHom.ker ≃* Multiplicative (ZMod 3)) := by
  let : Finite Presentation := finite_presentation hinj
  exact Multiplier.source_kernel_equiv_three_of_bound_and_triple_cover f hf hbound
    (cover hinj) (projection_kernel_card hinj hz)

end Sporadic.Janko3.TripleCover
