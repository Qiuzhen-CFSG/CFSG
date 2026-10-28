module
public import Theory.Frattini.CentralDerived
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags

/-!
# Central Frattini subgroup in the original distance-four core

At critical distance four, MS93 (4.6.9) puts the commutator core inside
the radius-two group V and identifies V-prime with the natural elementary
subgroup U. Since U is central in the core, its derived subgroup is central
of exponent two. The commutator-and-squares Frattini formula therefore
places the core's Frattini subgroup in its center.

This uses the source radius facts through (4.6.10); no classification of
core/U or elimination of the fixed quotient kernel is needed. The conclusion
excludes C.1.34(4), where the center is strictly below the Frattini subgroup.
Source: Meierfrankenfeld--Stellmacher (1993), (4.6.9), printed p.908.
-/

public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The original binary distance-four core has central Frattini subgroup. -/
theorem core_frattini_le_center_of_distance_four
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4) :
    frattini (core R (alpha R)) ≤ center (core R (alpha R)) := by
  let C := core R (alpha R)
  let facts := Flags.radiusFacts source geometry common hb
    (earlyFacts source geometry common hb)
  have hCQ : C ≤ Q R (alpha R) := core_le_Q source
  have hCS : C ≤ stabilizer R (alpha R) := hCQ.trans (fun _ hx => hx.1)
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite C := Finite.of_injective (inclusion hCS) (inclusion_injective hCS)
  have hp : IsPGroup 2 C := (Q_isPGroup R source.two_group source.core_le _ rfl).to_le hCQ
  have hd : ⁅C,C⁆ ≤ U R (alpha R) := by
    rw [← facts.radius_derived (alpha R) rfl]
    exact commutator_mono (facts.core_le_radius _ rfl) (facts.core_le_radius _ rfl)
  have hmap : (_root_.commutator C).map C.subtype = ⁅C,C⁆ := by
    rw [show _root_.commutator C = ⁅(⊤ : Subgroup C),⊤⁆ from rfl, map_commutator,
      ← MonoidHom.range_eq_map, range_subtype]
  have hdc : ∀ x ∈ _root_.commutator C, (x : FreeAmalgam R) ∈ U R (alpha R) := by
    intro x hx
    exact hd (hmap ▸ mem_map_of_mem C.subtype hx)
  apply frattini_le_center_of_central_involutory_commutators hp
  · intro x hx
    obtain ⟨y, hy, he⟩ := U_le_center_core source geometry common (hdc x hx)
    exact (Subtype.ext he : y = x) ▸ hy
  · intro x hx
    apply Subtype.ext
    exact congrArg (fun u : U R (alpha R) => (u : FreeAmalgam R))
      (U_square source geometry common ⟨x, hdc x hx⟩)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
