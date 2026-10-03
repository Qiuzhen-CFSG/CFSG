module
public import Stellmacher.SectionTen.TenOneCenterPointCentralizerType
public import Stellmacher.SectionTen.TenOneSmallCentralizerElementary
public import Theory.GroupTheory.OddCoreKleinFourCentralizers

/-!
# The odd core of an ambient small-case involution centralizer

For a point a of the actual elementary Wstar outside the middle center,
the full ambient centralizer C_H(embedding a) has trivial odd core. No
solvability hypothesis on that centralizer is assumed.

Apply the general Klein-four centralizer theorem to the image of the
middle four-center. It centralizes a because it lies in the middle-core
center. Its order and elementary structure transport through the supplied
embedding, and the native middle-center point theorem gives characteristic
two for each nonidentity point's full ambient centralizer. Wstar supplies
the involution order of a, with nonidentity forced by a lying outside the
middle center. Every group and point is the original native object.

Source: Stellmacher (10.1)(a3), printed p.62, the odd-core elimination in
the paragraph preceding assertion (10). The subsequent solvability
contradiction and containment use separate normalizer and local-core results.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_centralizer_odd_core
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (a : G) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    a ∈ Wstar → a ∉ ZAt ctx.Γ middle →
      pPrimeCore 2 (Subgroup.centralizer ({embedding a} : Set H)) = ⊥ := by
  let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
    GeneratedNeighborhoodV ctx.Γ middle
  let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
  change a ∈ Wstar → a ∉ ZAt ctx.Γ middle → _
  intro haW haZ
  let Z := ZAt ctx.Γ middle
  let ZH := Z.map embedding
  let _ : IsElementaryAbelian 2 Wstar :=
    (ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel).2.1
  let _ : IsElementaryAbelian 2 Z := by
    change IsElementaryAbelian 2 (ZAt ctx.Γ middle)
    rw [(sectionTenOpeningData ctx middle hpath).center_omega]
    exact omegaOneCenterAmbient_elementaryAbelian _
  let _ : IsElementaryAbelian 2 ZH := IsElementaryAbelian.map embedding
  have hZcard : Nat.card ZH=4 := by
    rw [card_map_of_injective ctx.embedding_injective]
    exact (sectionTenOpeningData ctx middle hpath).center_card
  have ha2 : a^2=1 := elemPow_eq_one_of_isElementaryAbelian (p:=2) (A:=Wstar) a haW
  have haord : orderOf (embedding a)=2 := by
    apply orderOf_eq_prime
    · rw [← map_pow,ha2,map_one]
    · intro hh
      apply haZ
      have heq : a=1 := ctx.embedding_injective (hh.trans (map_one embedding).symm)
      exact heq ▸ (ZAt ctx.Γ middle).one_mem
  have hZcentral : Z ≤ centralizer (QAt ctx.Γ middle:Set G) := by
    change ZAt ctx.Γ middle ≤ _
    rw [(sectionTenOpeningData ctx middle hpath).center_omega]
    exact (omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _)
  have hZa : ZH ≤ centralizer ({embedding a}:Set H) := by
    rintro _ ⟨z,hz,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg embedding
      ((mem_centralizer_iff.mp (hZcentral hz) a haW.1).symm)
  apply pPrimeCore_centralizer_eq_bot_of_klein_four (embedding a) haord ZH hZcard hZa
  rintro _ ⟨v,hv,rfl⟩ hvne
  exact ten_one_center_point_centralizer_characteristic_two ctx middle hpath v hv
    (fun hh => hvne (hh ▸ map_one embedding))

end Stellmacher.SectionTen