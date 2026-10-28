module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.Notation
public import Theory.SpecificGroups.Suzuki.StandardSubgroups
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.GroupTheory.PResidual.ThreeFree
public import Theory.GroupTheory.PGroup.OmegaAmbient

/-!
# The actual paired Suzuki orbit and its lifted Borel

The component orbit is literally ⟨K^{Tᵥ}⟩, and its Sylow intersection is
Tᵥ ∩ ⟨K^{Tᵥ}⟩. A marking is a genuine isomorphism of the central quotient
with two concrete Suzuki matrix groups. The lifted Borel is the inverse
image of the product of their standard Borels, with its ambient embedding
retained. Its kernel is the full center, including the Sz(8) cover case.

The later geometry must choose a marking aligned with the Sylow intersection.
That alignment, the Thompson calculation and the cubic field action are
not asserted here. The center being a two-group is an explicit earlier
multiplier input for the three-free calculation.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927 (PDF p.944).
The model parameter r used here has source field exponent m = 2r+1.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
open Subgroup BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G]

def orbit (T K : Subgroup G) (v : G) : Subgroup G :=
  conjugateSpanBy K (Tv T v)

def intersection (T K : Subgroup G) (v : G) : Subgroup G :=
  Tv T v ⊓ orbit T K v

def omega (T K : Subgroup G) (v : G) : Subgroup G :=
  omegaOneAmbient (intersection T K v)

structure Marking (T K : Subgroup G) (v : G) where
  parameter : ℕ
  positive : 0 < parameter
  equiv : (orbit T K v ⧸ center (orbit T K v)) ≃*
    (SuzukiMatrixGroup parameter × SuzukiMatrixGroup parameter)

namespace Marking
variable {T K : Subgroup G} {v : G} (d : Marking T K v)

def quotientMap : orbit T K v →*
    (SuzukiMatrixGroup d.parameter × SuzukiMatrixGroup d.parameter) :=
  d.equiv.toMonoidHom.comp (QuotientGroup.mk' (center (orbit T K v)))

def borelInOrbit : Subgroup (orbit T K v) :=
  ((SuzukiBorelSubgroup d.parameter).prod (SuzukiBorelSubgroup d.parameter)).comap
    d.quotientMap

def borel : Subgroup G := d.borelInOrbit.map (orbit T K v).subtype

theorem quotientMap_surjective : Function.Surjective d.quotientMap :=
  d.equiv.surjective.comp (QuotientGroup.mk'_surjective _)

theorem quotientMap_ker : d.quotientMap.ker = center (orbit T K v) := by
  ext x
  change d.equiv (QuotientGroup.mk' _ x) = 1 ↔ x ∈ center (orbit T K v)
  rw [← d.equiv.map_one, d.equiv.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

theorem borel_image : d.borelInOrbit.map d.quotientMap =
    (SuzukiBorelSubgroup d.parameter).prod (SuzukiBorelSubgroup d.parameter) := by
  rw [borelInOrbit, map_comap_eq, MonoidHom.range_eq_top.mpr d.quotientMap_surjective,
    top_inf_eq]

theorem borel_le_orbit : d.borel ≤ orbit T K v := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem intersection_le_borel
    (h : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter)) :
    intersection T K v ≤ d.borel := by
  intro x hx
  refine ⟨⟨x, hx.2⟩, ?_, rfl⟩
  have hx' : (⟨x, hx.2⟩ : orbit T K v) ∈ (Tv T v).subgroupOf (orbit T K v) := hx.1
  have hh := h (mem_map_of_mem d.quotientMap hx')
  have hroot : SuzukiRootSubgroup d.parameter ≤ SuzukiBorelSubgroup d.parameter := by
    rw [suzukiBorelSubgroup_eq_sup]
    exact le_sup_left
  exact ⟨hroot hh.1, hroot hh.2⟩

include d in
theorem orbit_three_free [Finite G] (hZ : IsPGroup 2 (center (orbit T K v))) :
    ¬ 3 ∣ Nat.card (orbit T K v) := by
  have hq : ¬ 3 ∣ Nat.card (orbit T K v ⧸ center (orbit T K v)) := by
    rw [Nat.card_congr d.equiv.toEquiv, Nat.card_prod]
    exact fun h => (Nat.prime_three.dvd_mul.mp h).elim
      (suzukiMatrixGroup_three_free d.parameter d.positive)
      (suzukiMatrixGroup_three_free d.parameter d.positive)
  intro hd
  rw [← (center (orbit T K v)).card_mul_index] at hd
  rcases Nat.prime_three.dvd_mul.mp hd with hc | hi
  · obtain ⟨n, hn⟩ := hZ.exists_card_eq
    rw [hn] at hc
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hc)
  · exact hq ((center (orbit T K v)).index_eq_card ▸ hi)

theorem borel_three_free [Finite G] (hZ : IsPGroup 2 (center (orbit T K v))) :
    ¬ 3 ∣ Nat.card d.borel := by
  intro h
  exact d.orbit_three_free hZ (h.trans (card_dvd_of_injective
    (inclusion d.borel_le_orbit) (inclusion_injective _)))

end Marking
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
