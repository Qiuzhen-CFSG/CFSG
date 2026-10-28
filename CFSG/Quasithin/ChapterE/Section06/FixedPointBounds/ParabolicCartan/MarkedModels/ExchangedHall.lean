module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Construction
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Cyclic
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ExchangedHall.Borel
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ExchangedHall.Orbit
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ExchangedHall.HallArgument

/-!+# Hall control for exchanged characteristic-two components

The PSL₂ and Suzuki Borel calculations put the derived subgroup of the
marked overlap in its two-core. The source product and component calculus
then construct a subgroup N normal in the actual maximal overgroup M,
with M = NS and [N,N] ≤ O₂(M). Hall conjugacy in O₂(M)Y gives the exact
factorization S = O₂(M) N_S(Y), with the original Sylow subgroup unchanged.
An odd Hall subgroup embeds in the abelian section and is therefore abelian.

The source kernel remains core_X(M) = O₂(X), and all component images and
overlaps use its literal quotient map. No intrinsic witness, normality of
the original component, or Hall-control conclusion is an input. The last
theorem applies this construction to the independently proved cyclic torus.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.2.2(1a),
pp.215--216, E.6.27, p.257, and 4.4.13, pp.623--624.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open Subgroup ChapterB
universe u
variable {X : Type u} [Group X] [Finite X]

/-- Hall control constructed from the exact exchanged branch of E.2.2.
After recognition, the calculation needs no further SQTK classification. -/
theorem exchanged_hallControl {Kc : GroupClass.{u}} (_hX : IsSQTK Kc X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (_hn : 1 < generationParameter X) {K : Subgroup X} (hK : K.IsCComponent)
    (hqs : Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K))
    (_hgen : (⊤ : Subgroup X) = K ⊔ (S : Subgroup X))
    (_hquot : IsSQTK Kc (X ⧸ sourceKernel (minimalParabolicMax S hP)))
    (hc : ExchangedClauses (minimalParabolicMax S hP) K S)
    (hm : ExchangedModel (minimalParabolicMax S hP) K (generationParameter X)) :
    HallControl S hP := by
  obtain ⟨N, hNM, hn, hgen, hd⟩ := ExchangedHall.normal_section hc hK hqs
    (minimalParabolicMax_spec S hP).2 (ExchangedHall.model_overlap_commutator hm)
  exact ExchangedHall.hallControl_of_normal_section S hP N hNM hn hgen hd

/-- The actual E.6.27 intrinsic construction in the exchanged branch,
using the model's cyclic theorem and the constructed Hall control. -/
theorem exchanged_intrinsicHallCartan {Kc : GroupClass.{u}} (hX : IsSQTK Kc X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (hn : 1 < generationParameter X) {K : Subgroup X} (hK : K.IsCComponent)
    (hqs : Theory.GroupTheory.IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : (⊤ : Subgroup X) = K ⊔ (S : Subgroup X))
    (hquot : IsSQTK Kc (X ⧸ sourceKernel (minimalParabolicMax S hP)))
    (hc : ExchangedClauses (minimalParabolicMax S hP) K S)
    (hm : ExchangedModel (minimalParabolicMax S hP) K (generationParameter X)) :
    Nonempty (IntrinsicHallCartanData S hP (generationParameter X)) :=
  intrinsic_of_cyclic_and_hallControl S hP (by omega)
    (exchanged_hallControl hX S hP hn hK hqs hgen hquot hc hm) hm.cyclic

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
