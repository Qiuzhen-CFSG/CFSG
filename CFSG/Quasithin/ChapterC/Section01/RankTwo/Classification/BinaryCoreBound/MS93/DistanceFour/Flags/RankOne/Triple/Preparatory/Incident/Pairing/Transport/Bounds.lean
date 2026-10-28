module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Symmetry.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeAction
public import Theory.Frattini.BinarySquares
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# Finite incident seed bounds for MS93 (1.7)(i)

The normal closure of the incident seed lies in the radius layer. Its squares
therefore lie in the central layer by the early radius calculation, giving the
Frattini bound. The seed pairing lies in the image of Z_beta: the seed is in
V_beta, V_alpha is in Q_beta, and the earlier edge index bounds their commutator.
This image is a proper subgroup of the central natural group of order eight,
so its order is at most four. Properness uses the genuine fixed-core kernel:
its intersection with Z_alpha lies in Z_beta.

A zero pairing extends to the normal closure in the finite quotient. The
explicit moving containment then contradicts the critical midpoint triple.
This is the only additional input; its producer remains with the incident
source assembly. No later radius-derived equality is used.

Source: Meierfrankenfeld--Stellmacher (1993), (1.7)(i), pp.847--848,
and its application in (4.6.8), claim (3), printed p.906.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Quotient.Bounds
open Escape.PairingControl.FirstPairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable (source : LocalSource L R) (geometry : Geometry R)
  (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
  (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
  (d : M) (hd : flagIncident source i 1 d)

omit [Finite M] in
include common early in
/-- Every radius-image square lies in the actual central quotient image. -/
theorem radius_image_square_mem (x : image (V R (alpha R))) :
    (x : Carrier R) ^ 2 ∈ image (Z R (alpha R)) := by
  obtain ⟨y, hy, he⟩ := x.property
  have hs := Propagation.radius_square_mem_Z common early ⟨y, hy⟩
  exact ⟨y ^ 2, hs, by simpa only [map_pow] using congrArg (fun z => z ^ 2) he⟩

include common hkernel hd in
/-- The quotient normal closure retains the ambient radius containment. -/
theorem generated_seed_le_radius :
    RankOnePairing.generated (seed source i d) ≤ image (V R (alpha R)) := by
  rw [generated_seed source geometry common.large_distance i hkernel d hd]
  exact image_mono (Pairing.span_le_radius source geometry common.large_distance i hkernel d hd)

include common early hkernel hd in
/-- The finite two-group Frattini subgroup is controlled by the early square bound. -/
theorem seed_frattini_le :
    (frattini (RankOnePairing.generated (seed source i d))).map
      (RankOnePairing.generated (seed source i d)).subtype ≤ image (Z R (alpha R)) := by
  have hUV := generated_seed_le_radius source geometry common i hkernel d hd
  have hp : IsPGroup 2 (RankOnePairing.generated (seed source i d)) :=
    (RankOnePairing.extensionCore_isPGroup (extension source (1 : M)).projection).to_le
      (hUV.trans (radius_le_core source geometry common.large_distance 1))
  rw [hp.frattini_eq_closure_squares, map_le_iff_le_comap]
  apply (closure_le _).mpr
  rintro _ ⟨x, rfl⟩
  exact radius_image_square_mem source geometry common early ⟨x, hUV x.property⟩

include common early hkernel hd in
/-- The incident seed pairing lies in the central natural image. -/
theorem seed_commutator_le :
    ⁅seed source i d, image (V R (alpha R))⁆ ≤ image (Z R (alpha R)) := by
  have hQ := Pairing.seed_le_Q source geometry common.large_distance i hkernel d hd
  have hS := hQ.trans (show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1)
  change ⁅quotientImage (alpha R) (Pairing.seed source i d),
    quotientImage (alpha R) (V R (alpha R))⁆ ≤ _
  rw [← quotientImage_commutator _ _ _ hS (geometry.V_local _ rfl common.large_distance)]
  apply image_mono
  rw [commutator_comm]
  exact (commutator_mono le_rfl hQ).trans (early.commutator_le_Z _ rfl)

include common early hkernel hd in
/-- Vanishing would contradict the critical triple after normal-closure transfer. -/
theorem seed_commutator_nontrivial (p : FlagCriticalData source geometry i)
    (hmoving : ⁅V R (beta R), flagResidual source i⁆ ≤ Pairing.span source i d) :
    Nat.card (⁅seed source i d, image (V R (alpha R))⁆ : Subgroup (Carrier R)) ≠ 1 := by
  intro hcard
  have hzero := eq_bot_of_card_eq _ hcard
  have hgen : ⁅image (V R (alpha R)), RankOnePairing.generated (seed source i d)⁆ = ⊥ := by
    apply bot_unique
    apply commutator_normalClosure_le_of_normal
    exact (commutator_comm _ _).trans hzero |>.le
  rw [generated_seed source geometry common.large_distance i hkernel d hd] at hgen
  have hVS := geometry.V_local (alpha R) rfl common.large_distance
  have hSV := Pairing.span_le_radius source geometry common.large_distance i hkernel d hd
  have hD : ⁅V R (alpha R), Pairing.span source i d⁆ ≤ fixedCore R (alpha R) :=
    (quotient_commutator_eq_bot_iff _ _ _ hVS (hSV.trans hVS)).mp hgen
  have hZ : ⁅V R (alpha R), Pairing.span source i d⁆ ≤ Z R (alpha R) :=
    (commutator_mono le_rfl (hSV.trans (V_le_Q geometry common.large_distance _ rfl))).trans
      (early.commutator_le_Z _ rfl)
  have hc := (le_inf hZ hD).trans (Pairing.Z_inf_fixedCore_le_center source geometry)
  rw [commutator_comm] at hc
  apply p.middle_triple
  have hm : Z R p.middle ≤ V R (beta R) := by
    simpa only [firstFlagLayer, localConjugate_one] using p.middle_le_firstLayer
  exact (commutator_mono ((commutator_mono hm le_rfl).trans hmoving) le_rfl).trans hc

omit [Finite M] in
include common in
/-- The central quotient image has the order of the actual natural summand. -/
theorem central_image_card : Nat.card (image (Z R (alpha R))) = 8 := by
  let e := (naturalImageEquiv source geometry common (1 : M)).symm.trans
    (pullEquiv (1 : M) (U R (alpha R))
      ((DistanceEight.U_le_Z R _).trans (Z_le_stabilizer R _)))
  exact (Nat.card_congr e.toEquiv).trans (common.natural.card_at _ rfl)

include common in
/-- The fixed-core kernel on Z_alpha already lies in the edge center. -/
theorem central_fixed_le_edgeZ :
    Z R (alpha R) ⊓ fixedCore R (alpha R) ≤ Z R (beta R) := by
  rw [Early.edge_Z_eq_fixed common (alpha R) (beta R) rfl (base_adjacent R)]
  refine le_inf inf_le_left ?_
  intro x hx q hq
  obtain ⟨z, hz, rfl⟩ := Pairing.Z_inf_fixedCore_le_center source geometry hx
  exact congrArg Subtype.val ((mem_center_iff.mp hz)
    ⟨q, hq.2 (alpha R) (adjacent_symm R (base_adjacent R))⟩)

include common early in
/-- Killing the fixed core cannot collapse the proper edge-center inclusion. -/
theorem edge_image_ne_central_image : image (Z R (beta R)) ≠ image (Z R (alpha R)) := by
  intro heq
  have hZ : Z R (alpha R) ≤ Z R (beta R) := by
    intro x hx
    let xS : stabilizer R (alpha R) := ⟨x, Z_le_stabilizer R _ hx⟩
    have him : quotientMap (alpha R) xS ∈ image (Z R (alpha R)) := ⟨xS, hx, rfl⟩
    rw [← heq] at him
    obtain ⟨y, hy, he⟩ := him
    have hdiv : (y : FreeAmalgam R) / x ∈ fixedCore R (alpha R) :=
      (QuotientGroup.eq_iff_div_mem.mp he : y / xS ∈ denominator (alpha R))
    have hdivZ : (y : FreeAmalgam R) / x ∈ Z R (alpha R) :=
      (Z R (alpha R)).div_mem (Early.edge_Z_le _ _ rfl (base_adjacent R) hy) hx
    have hdivB := central_fixed_le_edgeZ source geometry common ⟨hdivZ, hdiv⟩
    have hh := (Z R (beta R)).inv_mem ((Z R (beta R)).mul_mem ((Z R (beta R)).inv_mem hy) hdivB)
    simpa only [subtype_apply, div_eq_mul_inv, inv_mul_cancel_left, inv_inv] using hh
  have hh := early.edge_Z_index (alpha R) (beta R) rfl (base_adjacent R)
  rw [relIndex_eq_one.mpr hZ] at hh
  omega

include common early in
/-- The edge-center image is a proper subgroup of the natural group of order eight. -/
theorem edge_image_card_le_four : Nat.card (image (Z R (beta R))) ≤ 4 := by
  have hle : image (Z R (beta R)) ≤ image (Z R (alpha R)) :=
    image_mono (Early.edge_Z_le _ _ rfl (base_adjacent R))
  have hdiv : Nat.card (image (Z R (beta R))) ∣ 8 := by
    rw [← central_image_card source geometry common]
    exact card_dvd_of_le hle
  have hne : Nat.card (image (Z R (beta R))) ≠ 8 := by
    intro hcard
    apply edge_image_ne_central_image source geometry common early
    exact eq_of_le_of_card_ge hle (by rw [hcard, central_image_card source geometry common])
  have hmem := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

include common early hkernel hd in
/-- The entire seed pairing lands in the smaller edge-center image. -/
theorem seed_commutator_le_edge_image :
    ⁅seed source i d, image (V R (alpha R))⁆ ≤ image (Z R (beta R)) := by
  have hX := Pairing.seed_le_firstLayer source geometry common.large_distance i hkernel d hd
  have hXS := hX.trans (edgeRadius_le_stabilizer geometry common.large_distance)
  change ⁅quotientImage (alpha R) (Pairing.seed source i d),
    quotientImage (alpha R) (V R (alpha R))⁆ ≤ _
  rw [← quotientImage_commutator _ _ _ hXS (geometry.V_local _ rfl common.large_distance)]
  apply image_mono
  have hVQ : V R (alpha R) ≤ Q R (beta R) :=
    (V_le_Q geometry common.large_distance _ rfl).trans
      (Q_le_adjacent_h R rfl (base_adjacent R))
  exact (commutator_mono hX hVQ).trans
    (edgeRadius_commutator_le_edgeZ geometry common.large_distance early)

include common early hkernel hd in
/-- The exact upper bound needed by the binary source application of (1.7). -/
theorem seed_commutator_card_le_four :
    Nat.card (⁅seed source i d, image (V R (alpha R))⁆ : Subgroup (Carrier R)) ≤ 4 :=
  (card_le_of_le (seed_commutator_le_edge_image source geometry common early i hkernel d hd)).trans
    (edge_image_card_le_four source geometry common early)

include common early hkernel hd in
/-- All four finite seed bounds consumed by `sourceData_of_bounds`.
The moving containment is explicit and must be supplied by the source assembly. -/
theorem seed_bounds (p : FlagCriticalData source geometry i)
    (hmoving : ⁅V R (beta R), flagResidual source i⁆ ≤ Pairing.span source i d) :
    (frattini (RankOnePairing.generated (seed source i d))).map
        (RankOnePairing.generated (seed source i d)).subtype ≤ image (Z R (alpha R)) ∧
      ⁅seed source i d, image (V R (alpha R))⁆ ≤ image (Z R (alpha R)) ∧
      Nat.card (⁅seed source i d, image (V R (alpha R))⁆ : Subgroup (Carrier R)) ≠ 1 ∧
      Nat.card (⁅seed source i d, image (V R (alpha R))⁆ : Subgroup (Carrier R)) ≤ 4 :=
  ⟨seed_frattini_le source geometry common early i hkernel d hd,
    seed_commutator_le source geometry common early i hkernel d hd,
    seed_commutator_nontrivial source geometry common early i hkernel d hd p hmoving,
    seed_commutator_card_le_four source geometry common early i hkernel d hd⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Quotient.Bounds
