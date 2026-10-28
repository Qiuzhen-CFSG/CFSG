module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Pairing.Module.Fixed

/-!
# Full first-parabolic fixed points in the source central layer

The already proved opposite fixed-point calculation determines the marked
orientation: the opposite actor is the point parabolic, so the first actor
has no fixed vector on the actual natural U_alpha. The source central
splitting then puts its fixed points on all of Z_alpha in Z(G_alpha).
This uses the original marked action and no flag-control conclusion.

Source: Meierfrankenfeld--Stellmacher (1993), final paragraph of (4.6.8),
printed p.908; the opposite fixed-point calculation uses (1.7)(i), p.847.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
open RankOnePairing
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof
open Propagation.Pairing
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The first full actor has no fixed vector in the actual natural summand. -/
theorem natural_fixed_first_eq_bot (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R)) :
    U R (alpha R) ⊓ centralizer (flagParabolic source i : Set (FreeAmalgam R)) = ⊥ := by
  let e := pairingExtension source
  let n : NaturalFactor e.projection (component e.projection e.flag)
      (naturalLayer (R := R)) ⊥ := naturalCoordinates common
  have hL : (component e.projection e.flag).map e.projection = ⊤ :=
    component_map e.projection e.base.surjective e.flag
  have hop : fixedSpace (markedParabolic n.marking e.flag (!i)) ≠ ⊥ := by
    intro h
    apply opposite_fixed_nonzero common early i hkernel
    apply (coordinateImage_eq_bot_iff n inf_le_left).mp
    have he := coordinateImage_centralizer n hL (localResidual (localParabolic e (!i)))
    rw [localResidual_map] at he
    exact he.trans h
  have hf : fixedSpace (markedParabolic n.marking e.flag i) = ⊥ := by
    obtain ⟨k, hp | hp⟩ := marked_pair n.marking e.flag i
    · exfalso
      apply hop
      rw [hp.2, fixedSpace_conj, line_fixed_bot, Subgroup.map_bot]
    · rw [hp.1, fixedSpace_conj, line_fixed_bot, Subgroup.map_bot]
  have hpar : (parabolic source.projection source.flag i).map source.projection =
      modelParabolic source.flag i :=
    map_comap_eq_self_of_surjective source.projection_surjective _
  have hc : naturalLayer (R := R) ⊓
      centralizer (parabolic source.projection source.flag i : Set M) = ⊥ := by
    apply (coordinateImage_eq_bot_iff n inf_le_left).mp
    rw [coordinateImage_centralizer n hL]
    change fixedSpace (((parabolic source.projection source.flag i).map source.projection).map
      n.marking.toMonoidHom) = ⊥
    rw [hpar]
    exact hf
  apply eq_bot_iff.mpr
  rintro x ⟨hx, hfix⟩
  obtain ⟨u, hu, rfl⟩ := (show x ∈ (naturalLayer (R := R)).map (embedM R) from (map_naturalLayer (R := R)).symm ▸ hx)
  have hum : u ∈ naturalLayer (R := R) ⊓
      centralizer (parabolic source.projection source.flag i : Set M) := by
    refine ⟨hu, ?_⟩
    intro a ha
    apply embedM_injective R
    simpa only [map_mul] using hfix (embedM R a) (mem_map_of_mem (embedM R) ha)
  rw [hc] at hum
  exact mem_bot.mpr (by rw [mem_bot.mp hum, map_one])

/-- Fixed points of the first full parabolic in Z_alpha are central in G_alpha. -/
theorem full_actor_fixed_Z_le_center (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R)) :
    Z R (alpha R) ⊓ centralizer (flagParabolic source i : Set (FreeAmalgam R)) ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
  let F := Z R (alpha R) ⊓ centralizer (stabilizer R (alpha R) : Set (FreeAmalgam R))
  let s : BinaryNaturalStructure source :=
    ⟨common.X_eq_Z, common.natural, common.decomposition, common.disjoint⟩
  have hs : Z R (alpha R) = U R (alpha R) ⊔ F := s.decomposition_at _ rfl
  have hFU : F ≤ normalizer (U R (alpha R)) :=
    (inf_le_left.trans (Z_le_stabilizer R _)).trans (U_normalized _)
  have hFC : F ≤ centralizer (flagParabolic source i : Set (FreeAmalgam R)) :=
    inf_le_right.trans (centralizer_le (flagParabolic_le source i))
  intro x hx
  have hprod : x ∈ (U R (alpha R) : Set (FreeAmalgam R)) * (F : Set (FreeAmalgam R)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hFU, ← hs]
    exact hx.1
  obtain ⟨u, hu, f, hf, rfl⟩ := hprod
  have huc : u ∈ centralizer (flagParabolic source i : Set (FreeAmalgam R)) := by
    simpa only [mul_inv_cancel_right] using
      (centralizer (flagParabolic source i : Set (FreeAmalgam R))).mul_mem hx.2
        ((centralizer (flagParabolic source i : Set (FreeAmalgam R))).inv_mem (hFC hf))
  have hu1 : u = 1 := by
    have hh : u ∈ U R (alpha R) ⊓ centralizer (flagParabolic source i : Set (FreeAmalgam R)) := ⟨hu, huc⟩
    rw [natural_fixed_first_eq_bot source geometry common early i hkernel] at hh
    exact mem_bot.mp hh
  change u * f ∈ (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype
  rw [hu1, one_mul]
  refine ⟨⟨f, Z_le_stabilizer R _ hf.1⟩, mem_center_iff.mpr ?_, rfl⟩
  intro a
  exact Subtype.ext (hf.2 a a.property)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
