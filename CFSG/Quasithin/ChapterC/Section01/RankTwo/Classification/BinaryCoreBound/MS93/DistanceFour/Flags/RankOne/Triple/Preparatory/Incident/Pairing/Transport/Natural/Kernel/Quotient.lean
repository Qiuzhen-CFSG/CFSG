module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Natural.Kernel.Algebra
/-!
# Exact denominator transport for the incident local span

The original flag denominator is the preimage of the fixed space of the
first tilded residual. Its image in G_alpha/D_alpha remains exactly that
fixed preimage: two-perfect commutator idempotence removes D_alpha from the
lifted commutator bound. The quotient also preserves the intersection of
this denominator with the actual local span.

Consequently the global component-fixed kernel is contained in the flag
section kernel on that span. The reverse inclusion is proved under an
explicit local fixed-summand hypothesis: the intersection lies in the seed
and is fixed by the first full actor modulo Z_alpha. The contrary triple
fixes the seed under the opposite full actor. These two actors generate the
whole stabilizer, giving fixation under the actual global component.

The local fixed-summand hypothesis is not constructed in this module.
Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8)(3), printed p.906,
and the intrinsic kernel C/Z = C_(U/Z)(L) in (1.7), pp.847--848.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Kernel
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem residual_le_component (source : LocalSource L R) (i : Bool) :
    flagResidual source i ≤ Ltilde R (alpha R) := by
  rw [← flagResidual_sup source]
  cases i
  · exact le_sup_left
  · exact le_sup_right

private theorem pull_residual_perfect (source : LocalSource L R) (i : Bool)
    (d : M) (hd : flagIncident source i 1 d) :
    IsPPerfect 2 (pull (representative source i d hd) (flagResidual source i)) := by
  rw [← map_first_residual source i d hd, pull_map, pairing_parabolic,
    rankOne_parabolic_eq source.projection source.projection_surjective
      (by rw [source.projection_kernel]; exact pCore_isPGroup)]
  exact (isPPerfect_pResidual 2).of_surjective
    ((parabolic source.projection source.flag i).subtype.subgroupMap _)
    (MonoidHom.subgroupMap_surjective _ _)

private theorem qmap_kernel_centralizes (source : LocalSource L R) (i : Bool) (m : M) :
    (Quotient.qmap (R := R) m).ker ≤ centralizer (pull m (flagResidual source i) : Set M) := by
  rw [Quotient.qmap_kernel]
  intro x hx y hy
  apply embedding_injective m
  simp only [map_mul]
  exact hx.2 _ (residual_le_component source i hy)

private theorem map_localGenerated {G H : Type*} [Group G] [Group H]
    (f : G →* H) (P X : Subgroup G) (hXP : X ≤ P) :
    (RankOnePairing.localGenerated P X).map f =
      RankOnePairing.localGenerated (P.map f) (X.map f) := by
  open RankOnePairing RankOnePairing.Incidence in
    apply le_antisymm
    · apply map_le_iff_le_comap.mpr
      apply localGenerated_le_of_normalizes
      · exact ((map_le_iff_le_comap.mp (localGenerated_normalized (P.map f) (X.map f))).trans
          (le_normalizer_comap f))
      · exact map_le_iff_le_comap.mp (le_localGenerated _ _ (map_mono hXP))
    · apply localGenerated_le_of_normalizes
      · exact (map_mono (localGenerated_normalized P X)).trans (le_normalizer_map f)
      · exact map_mono (le_localGenerated P X hXP)

/-- The actual local closure is transported through the same incident marking. -/
theorem localSpan_image (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) :
    RankOnePairing.localGenerated (RankOnePairing.localParabolic
      (Quotient.extension source (representative source i d hd)) i) (Quotient.seed source i d) =
      Quotient.image (Pairing.localSpan source i d) := by
  let m := representative source i d hd
  have hseed : Pairing.seed source i d ≤ flagParabolic source i :=
    (Pairing.seed_le_firstLayer source geometry hlarge i hkernel d hd).trans
      (edgeRadius_le_flagParabolic source geometry hlarge i hkernel)
  have h := map_pull_localGenerated m (flagParabolic source i) (Pairing.seed source i d)
    (flagParabolic_le source i) hseed
  have hp : pull m (Pairing.localSpan source i d) =
      RankOnePairing.localGenerated (pull m (flagParabolic source i))
        (pull m (Pairing.seed source i d)) := by
    change pull m (RankOnePairing.localGenerated _ _) = _
    rw [← h, pull_map]
  rw [← Quotient.map_pull_qmap m, hp, map_localGenerated (Quotient.qmap m) (pull m (flagParabolic source i))
      (pull m (Pairing.seed source i d)) (comap_mono hseed),
    Quotient.map_pull_qmap, Quotient.map_pull_qmap, Quotient.first_actor]
  rfl

/-- The given denominator remains the exact residual-fixed preimage after killing D_alpha. -/
theorem sectionKernel_eq_commutatorPreimage (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) :
    sectionKernel source i = commutatorPreimage (Quotient.image (V R (beta R)))
      (Quotient.image (flagResidual source i)) (Quotient.image (Z R (alpha R))) := by
  let m := representative source i d hd
  let : (pull m (Z R (alpha R))).Normal := pull_normal m _ (Z_normalized R _)
  have hV := edgeRadius_le_stabilizer geometry hlarge
  have hres := (flagResidual_le source i).trans (flagParabolic_le source i)
  have hEA : pull m (flagResidual source i) ≤ normalizer (pull m (V R (beta R))) :=
    pull_normalizes m _ _ ((flagResidual_le source i).trans
      (flagParabolic_normalizes_edgeRadius source geometry hlarge i hkernel))
  let : IsElementaryAbelian 2 (V R (beta R)) :=
    edgeRadius_elementary geometry hlarge (alpha R) (beta R) rfl (base_adjacent R)
  have hA : IsPGroup 2 (pull m (V R (beta R))) :=
    (IsElementaryAbelian.isPGroup 2 (V R (beta R))).comap_of_injective
      (embedding R m) (embedding_injective m)
  have hh := map_commutatorPreimage (Quotient.qmap m) (Quotient.qmap_surjective m)
    (pull m (V R (beta R))) (pull m (flagResidual source i)) (pull m (Z R (alpha R)))
    (pull_residual_perfect source i d hd) hA hEA (qmap_kernel_centralizes source i m)
  rw [← pull_commutatorPreimage m _ _ _ hV hres (hV.trans (Z_normalized R _)),
    Quotient.map_pull_qmap, Quotient.map_pull_qmap, Quotient.map_pull_qmap,
    Quotient.map_pull_qmap] at hh
  exact hh

/-- Killing D_alpha commutes with the local intersection of the two kernels. -/
theorem image_sectionKernel_inf_localSpan (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) :
    Quotient.image (flagFixedPreimage source i ⊓ Pairing.localSpan source i d) =
      sectionKernel source i ⊓ Quotient.image (Pairing.localSpan source i d) := by
  let m := representative source i d hd
  have hker : pull m (V R (beta R)) ⊓ (Quotient.qmap (R := R) m).ker ≤
      pull m (flagFixedPreimage source i) := by
    rw [flagFixedPreimage, pull_commutatorPreimage m _ _ _
      (edgeRadius_le_stabilizer geometry hlarge)
      ((flagResidual_le source i).trans (flagParabolic_le source i))
      ((edgeRadius_le_stabilizer geometry hlarge).trans (Z_normalized R _))]
    apply le_commutatorPreimage inf_le_left
    exact (commutator_mono inf_le_right le_rfl).trans
      ((commutator_eq_bot_iff_le_centralizer.mpr
        (qmap_kernel_centralizes source i m)).le.trans bot_le)
  have h := map_inf_of_kernel (Quotient.qmap m)
    (pull m (flagFixedPreimage source i)) (pull m (Pairing.localSpan source i d))
    (pull m (V R (beta R)))
    (comap_mono (flagFixedPreimage_bounds source i).2)
    (comap_mono (localSpan_le_edgeRadius source geometry hlarge i hkernel d hd)) hker
  change (pull m (flagFixedPreimage source i ⊓ Pairing.localSpan source i d)).map
    (Quotient.qmap m) = _ at h
  simpa only [Quotient.map_pull_qmap, sectionKernel] using h

/-- The global component-fixed kernel is contained in the supplied section
kernel on the actual local span, with D_alpha explicitly accounted for. -/
theorem fixed_subgroupOf_le_sectionKernel (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) :
    (Quotient.fixed source i d hd).subgroupOf (RankOnePairing.localGenerated
      (RankOnePairing.localParabolic (Quotient.extension source (representative source i d hd)) i)
      (Quotient.seed source i d)) ≤
    (sectionKernel source i).subgroupOf (RankOnePairing.localGenerated
      (RankOnePairing.localParabolic (Quotient.extension source (representative source i d hd)) i)
      (Quotient.seed source i d)) := by
  rw [localSpan_image source geometry hlarge i hkernel d hd]
  have hV := Quotient.image_mono (localSpan_le_edgeRadius source geometry hlarge i hkernel d hd)
  have hres : Quotient.image (flagResidual source i) ≤ RankOnePairing.component
      (Quotient.projection source (representative source i d hd)) source.flag := by
    rw [Quotient.component_eq_image]
    exact Quotient.image_mono (residual_le_component source i)
  have hh : Quotient.fixed source i d hd ⊓ Quotient.image (Pairing.localSpan source i d) ≤
      sectionKernel source i := by
    rw [sectionKernel_eq_commutatorPreimage source geometry hlarge i hkernel d hd]
    exact le_commutatorPreimage (inf_le_right.trans hV)
      ((commutator_mono inf_le_left hres).trans
        (RankOnePairing.Incidence.fixedPreimage_commutator _ _ _))
  intro x hx
  exact hh ⟨hx, x.property⟩

/-- The exact denominator equality reduces to global fixation of the literal
intersection, rather than equality of whole ambient denominators. -/
theorem sectionKernel_subgroupOf_eq_of_global_fixation
    (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d)
    (hglobal : ⁅flagFixedPreimage source i ⊓ Pairing.localSpan source i d,
      Ltilde R (alpha R)⁆ ≤ Z R (alpha R)) :
    (sectionKernel source i).subgroupOf (RankOnePairing.localGenerated
      (RankOnePairing.localParabolic (Quotient.extension source (representative source i d hd)) i)
      (Quotient.seed source i d)) =
    (Quotient.fixed source i d hd).subgroupOf (RankOnePairing.localGenerated
      (RankOnePairing.localParabolic (Quotient.extension source (representative source i d hd)) i)
      (Quotient.seed source i d)) := by
  apply le_antisymm _ (fixed_subgroupOf_le_sectionKernel source geometry hlarge i hkernel d hd)
  have hmap : ⁅Quotient.image (flagFixedPreimage source i ⊓ Pairing.localSpan source i d),
      RankOnePairing.component (Quotient.projection source (representative source i d hd))
        source.flag⁆ ≤ Quotient.image (Z R (alpha R)) := by
    rw [Quotient.component_eq_image]
    change ⁅Escape.PairingControl.FirstPairing.quotientImage (alpha R) _,
      Escape.PairingControl.FirstPairing.quotientImage (alpha R) _⁆ ≤ _
    rw [← Escape.PairingControl.FirstPairing.quotientImage_commutator (alpha R)
      (flagFixedPreimage source i ⊓ Pairing.localSpan source i d) (Ltilde R (alpha R))
      ((inf_le_left.trans (flagFixedPreimage_bounds source i).2).trans
        (edgeRadius_le_stabilizer geometry hlarge)) (map_subtype_le _)]
    exact Quotient.image_mono hglobal
  intro x hx
  change (x : Quotient.Carrier R) ∈ Quotient.fixed source i d hd
  apply (RankOnePairing.mem_fixedPreimage _ _ _ (x : Quotient.Carrier R)).mpr
  refine ⟨RankOnePairing.localGenerated_le_generated _ _ x.property, ?_⟩
  intro l hl
  have hxI : (x : Quotient.Carrier R) ∈
      Quotient.image (flagFixedPreimage source i ⊓ Pairing.localSpan source i d) := by
    rw [image_sectionKernel_inf_localSpan source geometry hlarge i hkernel d hd]
    refine ⟨hx, ?_⟩
    rw [← localSpan_image source geometry hlarge i hkernel d hd]
    exact x.property
  rw [commutator_comm] at hmap
  exact hmap (commutator_mem_commutator hl hxI)


/-- The two full actors at the common incident marking generate G_alpha. -/
theorem incident_actors_generate (source : LocalSource L R) (i : Bool) (d : M)
    (hd : flagIncident source i 1 d) :
    flagParabolic source i ⊔ localFlagActor source (!i) d = stabilizer R (alpha R) := by
  have hg : RankOnePairing.localParabolic (Transport.extension source) i ⊔
      RankOnePairing.localParabolic (Transport.extension source) (!i) = ⊤ := by
    cases i
    · exact RankOnePairing.localParabolic_generation _
    · simpa only [Bool.not_true, sup_comm] using
        RankOnePairing.localParabolic_generation (Transport.extension source)
  have hh := congrArg (Subgroup.map (embedding R (representative source i d hd))) hg
  rwa [Subgroup.map_sup, map_first_actor source i d hd, map_second_actor source i d hd,
    ← MonoidHom.range_eq_map, embedding_range] at hh

/-- A local fixed-summand calculation suffices: its elements lie in the seed
and are fixed by the first full actor. The contrary triple supplies fixation
by the opposite full actor, and their actual generation gives global fixation. -/
theorem sectionKernel_subgroupOf_eq_of_local_fixed_summand
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d)
    (htriple : ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
      localFlagResidual source (!i) d⁆ ≤ Z R (alpha R))
    (hseed : flagFixedPreimage source i ⊓ Pairing.localSpan source i d ≤ Pairing.seed source i d)
    (hfirst : ⁅flagFixedPreimage source i ⊓ Pairing.localSpan source i d,
      flagParabolic source i⁆ ≤ Z R (alpha R)) :
    (sectionKernel source i).subgroupOf (RankOnePairing.localGenerated
      (RankOnePairing.localParabolic (Quotient.extension source (representative source i d hd)) i)
      (Quotient.seed source i d)) =
    (Quotient.fixed source i d hd).subgroupOf (RankOnePairing.localGenerated
      (RankOnePairing.localParabolic (Quotient.extension source (representative source i d hd)) i)
      (Quotient.seed source i d)) := by
  apply sectionKernel_subgroupOf_eq_of_global_fixation source geometry common.large_distance i hkernel d hd
  let C := flagFixedPreimage source i ⊓ Pairing.localSpan source i d
  have hsecond : ⁅C, localFlagActor source (!i) d⁆ ≤ Z R (alpha R) :=
    (commutator_mono hseed le_rfl).trans
      (seed_commutator_le_Z source geometry common early i hkernel d hd htriple)
  have hgen : stabilizer R (alpha R) ≤
      commutatorPreimage (stabilizer R (alpha R)) C (Z R (alpha R)) := by
    rw [← incident_actors_generate source i d hd]
    exact sup_le (le_commutatorPreimage le_sup_left (by rwa [commutator_comm]))
      (le_commutatorPreimage le_sup_right (by rwa [commutator_comm]))
  rw [commutator_comm]
  exact (commutator_mono ((show Ltilde R (alpha R) ≤ stabilizer R (alpha R) from
    map_subtype_le _).trans hgen) le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ (Z_normalized R _))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural.Kernel
