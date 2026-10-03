module
public import Stellmacher.SectionTen.OpeningData
public import Stellmacher.SectionFiveToSeven.LocalResidualCoreContainment
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# The middle residual modulo its two-core is a three-group

In the actual Section Ten configuration, the intrinsic quotient of the
middle residual by its two-core is a three-group. Only the original
context and the offset-two middle vertex are required.

Restrict the actual middle SL₂(2) quotient projection to its residual.
The residual-core intersection identity identifies the restricted kernel
with the intrinsic residual two-core, so the first isomorphism theorem
makes the quotient order divide six. The local residual quotient has
odd order, leaving order one or three. No choice of an odd complement
or nontriviality of this quotient is assumed.

This supplies the acting three-group in the large middle residual escape
and join-index arguments of Stellmacher (10.1)(b2), printed pp.60,65,
using the standing middle quotient from printed p.59.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u

public theorem ten_one_middle_residual_quotient_isThreeGroup
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle) :
    IsPGroup 3 (EAt ctx.Γ middle ⧸ pCore 2 (EAt ctx.Γ middle)) := by
  let M := GAt ctx.Γ middle
  let E := EAt ctx.Γ middle
  let Q := QAt ctx.Γ middle
  let U := twoCoreIn E
  have hE : E = twoResidualIn M := ctx.Γ.twoResidualAt_def _
  have hEM : E ≤ M := hE ▸ twoResidualIn_le M
  have hU : U = E ⊓ Q := by
    change twoCoreIn E = E ⊓ ctx.Γ.twoCoreAt middle
    rw [ctx.Γ.twoCoreAt_def,hE,residual_core_eq_inter_core]
    rfl
  obtain ⟨projection,hsurj,hker⟩ := (sectionTenOpeningData ctx middle hpath).quotient_model
  let f := projection.comp (inclusion hEM)
  have hfker : f.ker = pCore 2 E := by
    ext e
    constructor
    · intro he
      have he' : inclusion hEM e ∈ projection.ker := he
      rw [hker] at he'
      have hq : (e:G) ∈ Q := he'
      have hu : (e:G) ∈ U := hU.symm ▸ ⟨e.property,hq⟩
      obtain ⟨x,hx,hxe⟩ := hu
      exact (show x=e from Subtype.ext hxe) ▸ hx
    · intro he
      have hu : (e:G) ∈ U := mem_map_of_mem E.subtype he
      have hq : (e:G) ∈ Q := (hU ▸ hu).2
      change inclusion hEM e ∈ projection.ker
      rw [hker]
      exact hq
  have hcard : Nat.card (E ⧸ pCore 2 E) = Nat.card f.range := by
    exact (Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hfker.symm).toEquiv).trans
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv)
  have hsix : Nat.card SL2Two = 6 := by
    obtain ⟨equiv⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
    rw [Nat.card_congr equiv.toEquiv,Nat.card_perm,Nat.card_fin]
    norm_num
  have hdiv : Nat.card (E ⧸ pCore 2 E) ∣ 6 := by
    rw [hcard,←hsix]
    exact f.range.card_subgroup_dvd_card
  obtain ⟨_,hfirst,_,_⟩ := sectionTenOpeningGeometry ctx middle hpath
  have hodd : Odd (Nat.card (E ⧸ pCore 2 E)) := by
    rw [hE]
    exact local_residual_core_quotient_odd ctx.sectionSeven ctx.Γ middle
      ctx.criticalPath.firstStep ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hfirst) M le_rfl
  have hdivThree : Nat.card (E ⧸ pCore 2 E) ∣ 3 :=
    hodd.coprime_two_right.dvd_of_dvd_mul_left hdiv
  have hchoices : Nat.card (E ⧸ pCore 2 E) = 1 ∨ Nat.card (E ⧸ pCore 2 E) = 3 := by
    exact (Nat.dvd_prime Nat.prime_three).mp hdivThree
  rcases hchoices with hone | hthree
  · exact IsPGroup.of_card (p:=3) (n:=0) (by simpa using hone)
  · exact IsPGroup.of_card (p:=3) (n:=1) (by simpa using hthree)

end Stellmacher.SectionTen
