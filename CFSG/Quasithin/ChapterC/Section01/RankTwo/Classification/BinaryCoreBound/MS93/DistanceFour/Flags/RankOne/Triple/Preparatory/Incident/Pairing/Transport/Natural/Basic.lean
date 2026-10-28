module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.DualGeometry.ResidualGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Propagation.Pairing.Module.Fixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Symmetry.Algebra

/-!
# Moving containment and fixed vectors for the incident pairing

The opposite parabolic core normally generates the first full actor. Its
edge-layer displacement therefore generates a local span containing the
whole first-actor displacement, before taking any quotient. Under the
contrary triple hypothesis, the incident supplement and the earlier edge
commutator calculation make the seed fixed modulo Z_alpha by the full
opposite actor. This gives the literal fixed-preimage bound used in (1.7).

A nonzero opposite fixed vector is transported through the common incident
representative and survives the quotient by D_alpha because that quotient
is injective on U_alpha. The transported flag-section denominator is named
separately; these results do not identify it with the global fixed preimage
on the local span or construct the remaining rank-one factor.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8)(3), printed p.906,
and the module hypotheses of (1.7)(i), pp.847--848.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

omit [Finite M] in
/-- The transported denominator of the given flag section. Identifying its
restriction to the local span with the global fixed preimage is a separate
mathematical obligation. -/
noncomputable def sectionKernel (source : LocalSource L R) (i : Bool) :
    Subgroup (Quotient.Carrier R) :=
  Quotient.image (flagFixedPreimage source i)

private theorem commutator_join_le {G : Type*} [Group G]
    (A B K N : Subgroup G) (hA : A ≤ normalizer N) (hB : B ≤ normalizer N)
    (ha : ⁅A,K⁆ ≤ N) (hb : ⁅B,K⁆ ≤ N) : ⁅A ⊔ B,K⁆ ≤ N := by
  have h : A ⊔ B ≤ commutatorPreimage (A ⊔ B) K N :=
    sup_le (le_commutatorPreimage le_sup_left ha) (le_commutatorPreimage le_sup_right hb)
  exact (commutator_mono h le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (sup_le hA hB))

/-- The contrary triple and the incident supplement imply fixation of the
whole seed modulo the original Z-layer by the full opposite actor. -/
theorem seed_commutator_le_Z (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d)
    (htriple : ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
      localFlagResidual source (!i) d⁆ ≤ Z R (alpha R)) :
    ⁅Pairing.seed source i d, localFlagActor source (!i) d⁆ ≤ Z R (alpha R) := by
  have hVN := (edgeRadius_le_stabilizer geometry common.large_distance).trans (Z_normalized R _)
  have hKN := ((flagKernel_le source i).trans (flagParabolic_le source i)).trans (Z_normalized R _)
  have hRN := ((map_mono (flagResidual_le source (!i))) :
    localFlagResidual source (!i) d ≤ localFlagActor source (!i) d).trans
      ((localFlagActor_le_stabilizer source (!i) d).trans (Z_normalized R _))
  have hCV : ⁅V R (beta R), localFlagKernel source (!i) d⁆ ≤ V R (beta R) :=
    le_normalizer_iff_commutator_le_left.mp
      ((incidentKernel_le_flagParabolic source i d hd).trans
        (flagParabolic_normalizes_edgeRadius source geometry common.large_distance i hkernel))
  have hCK : ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆, flagKernel source i⁆ ≤
      Z R (alpha R) := by
    rw [hkernel]
    exact (commutator_mono hCV le_rfl).trans
      ((edgeRadius_commutator_le_edgeZ geometry common.large_distance early).trans
        (Early.edge_Z_le (alpha R) (beta R) rfl (base_adjacent R)))
  have hCA : ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
      localFlagActor source (!i) d⁆ ≤ Z R (alpha R) := by
    rw [← flagKernel_sup_incidentResidual source i d hd, commutator_comm]
    exact commutator_join_le _ _ _ _ hKN hRN
      (by rwa [commutator_comm]) (by rwa [commutator_comm])
  exact commutator_join_le _ _ _ _
    ((Z_le_stabilizer R _).trans (Z_normalized R _)) (hCV.trans hVN)
    (le_normalizer_iff_commutator_le_left.mp
      ((localFlagActor_le_stabilizer source (!i) d).trans (Z_normalized R _))) hCA

/-- The exact hfixed premise in the fixed-core quotient. -/
theorem seed_fixed (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d)
    (htriple : ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
      localFlagResidual source (!i) d⁆ ≤ Z R (alpha R)) :
    ⁅Quotient.seed source i d,
      RankOnePairing.localResidual (RankOnePairing.localParabolic
        (Quotient.extension source (representative source i d hd)) (!i))⁆ ≤
      Quotient.fixed source i d hd := by
  apply le_trans _ (RankOnePairing.le_fixedPreimage _ _ _ (Quotient.Z_le_seed source i d))
  rw [Quotient.localResidual_eq_parabolic, Quotient.second_actor]
  change ⁅Quotient.image (Pairing.seed source i d), Quotient.image (localFlagActor source (!i) d)⁆ ≤ _
  rw [Quotient.image, Quotient.image, ← Escape.PairingControl.FirstPairing.quotientImage_commutator _ _ _
    ((Pairing.seed_le_Q source geometry common.large_distance i hkernel d hd).trans (fun _ hx => hx.1))
    (localFlagActor_le_stabilizer source (!i) d)]
  exact Quotient.image_mono (seed_commutator_le_Z source geometry common early i hkernel d hd htriple)

private theorem localFacts_bot (e : RankOnePairing.Extension (M := M)) :
    RankOnePairing.Incidence.LocalFacts e ⊥ where
  core_le := RankOnePairing.extensionCore_le_localParabolic e
  core_eq j := (RankOnePairing.selectedCore_eq_localCore e j).symm
  parabolic_image := RankOnePairing.localParabolic_map e
  residual_image := RankOnePairing.localResidual_map e
  core_image := RankOnePairing.localCore_map e
  generation := RankOnePairing.localParabolic_generation e
  component_normal := RankOnePairing.component_normal e
  component_image := RankOnePairing.component_map _ e.base.surjective _
  z_central := bot_le
  z_irreducible := fun _ h _ => Or.inl (bot_unique h)

/-- The local closure stays in the original elementary edge group. -/
theorem localSpan_le_edgeRadius (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) :
    Pairing.localSpan source i d ≤ V R (beta R) :=
  RankOnePairing.Incidence.localGenerated_le_of_normalizes _ _ _
    (flagParabolic_normalizes_edgeRadius source geometry hlarge i hkernel)
    (Pairing.seed_le_firstLayer source geometry hlarge i hkernel d hd)

/-- The opposite core normally generates the first actor, so the local seed
closure contains the displacement of the entire full actor. -/
theorem actor_moving_le_localSpan (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) :
    ⁅V R (beta R), flagParabolic source i⁆ ≤ Pairing.localSpan source i d := by
  let m := representative source i d hd
  let e := Transport.extension source
  let P := RankOnePairing.localParabolic e i
  let K := RankOnePairing.selectedCore e (!i)
  let H := pull m (V R (beta R))
  let S := pull m (Pairing.localSpan source i d)
  have hP : P ≤ RankOnePairing.localGenerated P K := by
    have h := RankOnePairing.Incidence.DualGeometry.residual_generation (localFacts_bot e) i
    rw [← RankOnePairing.selectedCore_eq_localCore] at h
    have hr : RankOnePairing.localResidual P = P := by
      rw [show P = parabolic source.projection source.flag i from pairing_parabolic source i,
        RankOnePairing.localResidual,
        primeToResidual_parabolic_eq_top source.projection source.projection_surjective
          (by rw [source.projection_kernel]; exact pCore_isPGroup),
        ← MonoidHom.range_eq_map, range_subtype]
    change RankOnePairing.localResidual P ≤ RankOnePairing.localGenerated P K at h
    rwa [hr] at h
  have hV := edgeRadius_le_stabilizer geometry hlarge
  have hseed : Pairing.seed source i d ≤ flagParabolic source i :=
    (Pairing.seed_le_firstLayer source geometry hlarge i hkernel d hd).trans
      (edgeRadius_le_flagParabolic source geometry hlarge i hkernel)
  have hKH : ⁅K,H⁆ ≤ S := by
    have hs : ⁅V R (beta R), localFlagKernel source (!i) d⁆ ≤ Pairing.localSpan source i d :=
      le_sup_right.trans (RankOnePairing.le_localGenerated _ _ hseed)
    have hp := comap_mono (f := embedding R m) hs
    change pull m ⁅V R (beta R), localFlagKernel source (!i) d⁆ ≤ S at hp
    rw [pull_commutator m _ _ hV (localFlagKernel_le_stabilizer source (!i) d),
      ← map_second_core source i d hd, pull_map, commutator_comm] at hp
    exact hp
  have hPH : P ≤ normalizer H := by
    have hn := pull_normalizes m _ _
      (flagParabolic_normalizes_edgeRadius source geometry hlarge i hkernel)
    rw [← map_first_actor source i d hd, pull_map] at hn
    exact hn
  have hPS : P ≤ normalizer S := by
    have hn := pull_normalizes m _ _
      (RankOnePairing.Incidence.localGenerated_normalized (flagParabolic source i)
        (Pairing.seed source i d))
    change pull m (flagParabolic source i) ≤ normalizer S at hn
    rw [← map_first_actor source i d hd, pull_map] at hn
    exact hn
  have hKP : K ≤ P :=
    (show K ≤ RankOnePairing.commonSylow e from inf_le_left).trans
      (RankOnePairing.commonSylow_le_localParabolic e i)
  have hpre : RankOnePairing.localGenerated P K ≤ commutatorPreimage P H S :=
    RankOnePairing.Incidence.localGenerated_le_of_normalizes _ _ _
      (commutatorPreimage_normalized _ _ _ _ hPS P.le_normalizer hPH hPS)
      (le_commutatorPreimage hKP hKH)
  have hHS : ⁅H,P⁆ ≤ S := by
    rw [commutator_comm]
    exact (commutator_mono (hP.trans hpre) le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hPS)
  have hm := map_mono (f := embedding R m) hHS
  rw [map_commutator, map_pull m _ hV, map_first_actor source i d hd,
    map_pull m _ ((localSpan_le_edgeRadius source geometry hlarge i hkernel d hd).trans hV)] at hm
  exact hm

/-- The required unquotiented moving containment follows through the literal
local and global closures, without a quotient-containment substitute. -/
theorem moving_le_span (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) :
    ⁅V R (beta R), flagResidual source i⁆ ≤ Pairing.span source i d :=
  ((commutator_mono le_rfl (flagResidual_le source i)).trans
    (actor_moving_le_localSpan source geometry hlarge i hkernel d hd)).trans
      (Pairing.localSpan_le_span source i d)

omit [Finite M] in
/-- Conjugation by the common representative preserves the actual natural subgroup. -/
theorem pull_U (m : M) :
    pull m (U R (alpha R)) = Propagation.Pairing.naturalLayer (R := R) := by
  apply map_injective (embedding_injective m)
  rw [map_pull _ _ ((U_le_Z _).trans (Z_le_stabilizer R _)), map_embedding,
    Propagation.Pairing.map_naturalLayer]
  apply (mem_normalizer_iff_map_conj_eq.mp (U_normalized (alpha R) ?_)).symm
  rw [alpha, stabilizer_m_base]
  exact ⟨m, rfl⟩

/-- The full opposite actor retains a nonzero fixed vector after killing D_alpha. -/
theorem opposite_fixed_nonzero (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) :
    Quotient.image (Z R (alpha R)) ⊓
      centralizer (RankOnePairing.localResidual (RankOnePairing.localParabolic
        (Quotient.extension source (representative source i d hd)) (!i)) :
          Set (Quotient.Carrier R)) ≠ ⊥ := by
  let m := representative source i d hd
  have hr : RankOnePairing.localResidual (RankOnePairing.localParabolic (Transport.extension source) (!i)) =
      RankOnePairing.localParabolic (Transport.extension source) (!i) := by
    rw [pairing_parabolic, RankOnePairing.localResidual,
      primeToResidual_parabolic_eq_top source.projection source.projection_surjective
        (by rw [source.projection_kernel]; exact pCore_isPGroup),
      ← MonoidHom.range_eq_map, range_subtype]
  have hf := Propagation.Pairing.opposite_fixed_nonzero common early i hkernel
  change Propagation.Pairing.naturalLayer (R := R) ⊓ centralizer
    (RankOnePairing.localResidual (RankOnePairing.localParabolic (Transport.extension source) (!i)) : Set M) ≠ ⊥ at hf
  rw [hr, ← pull_U m] at hf
  obtain ⟨x, hx, hxne⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hf
  have hU : x ∈ pull m (U R (alpha R)) := hx.1
  have hqne : Quotient.qmap (R := R) m x ≠ 1 := by
    intro he
    have hh : Quotient.naturalImageMap m ⟨x, hU⟩ = 1 := Subtype.ext he
    have hh' := (Quotient.naturalImageMap_bijective source geometry common m).1
      (hh.trans (map_one (Quotient.naturalImageMap m)).symm)
    exact hxne (congrArg Subtype.val hh')
  intro hbot
  apply hqne
  apply Subgroup.mem_bot.mp
  rw [← hbot]
  constructor
  · rw [← Quotient.map_pull_qmap m]
    exact mem_map_of_mem _ (U_le_Z _ hU)
  · rw [Quotient.localResidual_eq_parabolic, ← Quotient.map_parabolic]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact (map_mul (Quotient.qmap m) a x).symm.trans
      ((congrArg (Quotient.qmap m) (hx.2 a ha)).trans (map_mul (Quotient.qmap m) x a))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Natural
