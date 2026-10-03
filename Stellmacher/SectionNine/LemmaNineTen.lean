module
public import Stellmacher.SectionNine.NineTenFiveContradiction
public import Stellmacher.SectionNine.NineTenLongDistanceExclusion
/-!
# Stellmacher (9.10): the critical distance is at most three

The original Section Nine statement and its ambient-retaining form follow
from the completed long-distance and distance-five arguments. No additional
containment, extraction, classification, or action hypothesis is imposed.

If the critical length exceeds three, odd critical-path geometry and the
proved upper bound force length five. Normalize one actual reversed
configuration, preserving its length and both geometric extraction packets.
The excluded-center branch forces the terminal center into the residual
neighborhood layer, while the contained-center branch contradicts that
inclusion via nilpotent saturation and the actual normal Sylow fixed space.
Thus length five is impossible. The original public theorem uses the existing
ambient-context adapter, preserving its name and statement.

Source: Stellmacher, Journal of Algebra 190 (1997), (9.10), printed pp.57–59
of `refs/files/stellmacher-n-group.pdf`. The geometric and module arguments
are proved in the imported small modules; this file is their final assembly.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem lemma_nine_ten_ambient
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) :
    ctx.criticalPath.length ≤ 3 := by
  by_contra! hb
  have hupper := nine_ten_length_le_five ctx
  have hlower := nine_ten_length_ge_five ctx.toLocalContext hb
  have hlength : ctx.criticalPath.length=5 := by
    change 5≤ctx.criticalPath.length at hlower
    omega
  obtain ⟨cp,hlen,hcomm,hterm,hfirst,neighbor,second,actor,E,A0,data,
    hsecond,hnew,hneighbor,hactor,hcenters,hactorComm,
    firstActor,firstE,firstA0,firstData,hfirstNew,hfirstActors,_⟩ :=
    nine_ten_normalized_reversed_configuration ctx hb
  let shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B :=
    {ctx with criticalPath:=cp,commutator_eq:=hcomm}
  have hshift : shifted.criticalPath.length=5 := by change cp.length=5; omega
  exact nine_ten_five_contradiction shifted hshift hterm hfirst
    neighbor second actor E A0 data hsecond hactor hactorComm hnew hneighbor
      hcenters firstActor firstE firstA0 firstData hfirstNew hfirstActors

/-- **Stellmacher (9.10).** Under the standing Section Nine hypotheses,
the critical distance is at most three. -/
public theorem lemma_nine_ten
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2) :
    ctx.criticalPath.length ≤ 3 :=
  lemma_nine_ten_ambient ctx.toAmbientContext

end Stellmacher.SectionNine
