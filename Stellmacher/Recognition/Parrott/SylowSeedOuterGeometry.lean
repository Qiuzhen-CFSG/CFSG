module

public import Stellmacher.Recognition.Parrott.SylowOuterSeed

/-!
# The outer involution already determined by a Sylow seed

The seed action on u gives [u,x²z]=t. Since the derived core is the second
center of the original two-core, a core element could only have a central
commutator with u. Thus x²z, and also x², lie outside that core. No relations
from (17)–(19) or global conjugacy class of x²z are used.

Source: Parrott (1972), §3, printed pp.678–680. The second-center argument
is also used for completed frames in CentralizerInvolutionSeed.lean.
-/

open Subgroup
open scoped commutatorElement
namespace Stellmacher.Recognition.ParrottSylowSeedData
variable {G : Type*} [Group G] {z : G} {e : ParrottSecondElementaryData z}
variable {n : ParrottNormalizerFusionData e} {caseTwo : Bool}
variable (f : ParrottSylowSeedData n caseTwo)

/-- The seed generator lies in the normalizer two-core since it centralizes t. -/
public theorem x_mem_normalizer_core :
    f.x ∈ (pCore 2 (normalizer (e.F : Set G))).map
      (normalizer (e.F : Set G)).subtype := by
  rw [n.core_eq_sylow_centralizer]
  exact ⟨f.x_mem_sylow, mem_centralizer_singleton_iff.mpr
    ((Tits.parrottCommutator_eq_one_iff _ _).mp f.relations.eq01_xt)⟩

/-- The forced involution belongs to the supplied Sylow subgroup. -/
public theorem square_mul_z_mem_sylow : f.x^2*z ∈ e.sylow :=
  (e.sylow : Subgroup G).mul_mem ((e.sylow : Subgroup G).pow_mem f.x_mem_sylow 2)
    (e.le_sylow e.z_mem_inf.2)

/-- The prescribed y lies outside the original two-core: its commutator
with u is t, whereas core commutators with the derived core lie in ⟨z⟩. -/
public theorem square_mul_z_not_mem_core [Finite G] (h : ParrottCentralizerHypotheses z) :
    (f.x^2*z) ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  have huE : f.u ∈ E := by
    change f.u ∈ (commutator J).map (H.subtype.comp J.subtype)
    rw [← f.derived_basis]
    exact subset_closure (by simp)
  obtain ⟨uJ, huD, hu⟩ := huE
  intro hy
  obtain ⟨yH, hyJ, hy⟩ := hy
  let yJ : J := ⟨yH, hyJ⟩
  obtain ⟨hZ, _, _, _, hupper, _, _, _⟩ := parrott_centralizer_structure z h
  have huU : uJ ∈ Subgroup.upperCentralSeries J 2 := hupper ▸ huD
  have hc : ⁅uJ, yJ⁆ ∈ center J := by
    simpa only [Subgroup.upperCentralSeries_one] using
      Subgroup.mem_upperCentralSeries_succ_iff.mp huU yJ
  have hct : ⁅f.u, (f.x^2*z)⁆ = n.t := by
    have hui : f.u⁻¹ = f.u := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using f.relations.u_sq)
    have hyi : (f.x^2*z)⁻¹ = (f.x^2*z) := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using f.relations.square_mul_z.1)
    have hconj := f.relations.square_mul_z_action.2.1
    rw [hyi] at hconj
    rw [commutatorElement_def, hui, hyi]
    calc
      f.u * (f.x^2*z) * f.u * (f.x^2*z) = f.u * ((f.x^2*z) * f.u * (f.x^2*z)) := by group
      _ = f.u * (f.u * n.t) := by rw [hconj]
      _ = n.t := by rw [← mul_assoc, ← pow_two, f.relations.u_sq, one_mul]
  apply n.t_not_mem_zpowers
  rw [← hZ]
  refine ⟨⁅uJ, yJ⁆, hc, ?_⟩
  change (H.subtype.comp J.subtype) ⁅uJ, yJ⁆ = n.t
  rw [map_commutatorElement, hu]
  change ⁅f.u, (yH : G)⁆ = n.t
  change (yH : G) = (f.x^2*z) at hy
  rw [hy, hct]

/-- The normalized Sylow coordinate y is an actual involution. -/
public theorem square_mul_z_order [Finite G] (h : ParrottCentralizerHypotheses z) : orderOf (f.x^2*z) = 2 := by
  apply orderOf_eq_prime_iff.mpr
  refine ⟨f.relations.square_mul_z.1, ?_⟩
  intro hy
  exact f.square_mul_z_not_mem_core h (hy ▸ one_mem _)

/-- The square itself lies outside the original two-core. -/
public theorem square_not_mem_core [Finite G] (h : ParrottCentralizerHypotheses z) :
    f.x^2 ∉ (pCore 2 (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype := by
  intro hx
  exact f.square_mul_z_not_mem_core h
    (mul_mem hx (e.le_core e.z_mem_inf.2))

end Stellmacher.Recognition.ParrottSylowSeedData
