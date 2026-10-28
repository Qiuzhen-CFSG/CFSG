module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.NaturalCore.LocalGeometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.NaturalCore.SourceQuotient

/-!
# The natural distance-two core estimates

Critical-pair normal generation supplies involution generation of the core.
The local commutator lies in the natural endpoint group and the actual edge
commutator, has order at most four, and escapes U in the non-Frattini branch.
Its normality in the core supplies an element outside U whose centralizer
inside the core has index at most two.

The local commutator and order calculations also construct the actual
equivariant surjection from core to the natural eight, with kernel U.
`extensionEstimates` assembles all three conclusions from `LocalSource`,
`Geometry`, distance two, `NaturalU` and the non-Frattini premise. The
quotient retains its independent automorphism marking; agreement with
the marking on U belongs to the subsequent central-extension argument.

The earlier assembly variant with an explicit conjugate-generation identity
and edge centralizer estimate is preserved for callers supplying those data.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the natural SL3 branch of (3.6), printed pp.870--871.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Assemble the extension estimates from an actual quotient, an explicit
conjugate-generation identity and an edge centralizer estimate. -/
theorem extensionEstimates_of_local_conjugates (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 2)
    (natural : NaturalU R source.projection)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    (quotient : NaturalCoreQuotient source)
    {a' t : Vertex R}
    (hc : CriticalPair R (alpha R) a' (geometry.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (ha't : Adjacent R a' t)
    (hgen : core R (alpha R) = ⨆ m : M,
      (⁅Q R (alpha R), Z R a'⁆).map (MulAut.conj (embedM R m)).toMonoidHom)
    (hindex : (centralizer ((⁅Z R a', Q R t⁆ : Subgroup (FreeAmalgam R)) :
      Set (FreeAmalgam R))).relIndex (Q R t) ≤ 2) :
    Nonempty (ExtensionEstimates source) := by
  exact ⟨{
    quotient := quotient
    small_centralizer :=
      small_centralizer_of_local_conjugates source geometry hb natural hlarge hat hgen hindex
    involution_generation :=
      involution_generation_of_local_conjugates geometry hb hc hat ha't hgen }⟩

/-- The natural non-Frattini branch at distance two supplies the actual
quotient, the small core centralizer and generation by involutions. -/
theorem extensionEstimates (source : LocalSource L R)
    (geometry : Geometry R) (hb : geometry.b R = 2)
    (natural : NaturalU R source.projection)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    Nonempty (ExtensionEstimates source) := by
  obtain ⟨quotient⟩ := exists_naturalCoreQuotient source geometry hb natural hlarge
  exact ⟨{
    quotient := quotient
    small_centralizer := small_centralizer source geometry hb natural hlarge
    involution_generation := involution_generation source geometry hb }⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.NaturalCore
