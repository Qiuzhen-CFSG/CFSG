module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Incident.Pairing.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Quotient

/-!
# The finite fixed-core quotient for the incident pairing

The marked finite stabilizer from `Transport` is divided by the actual
D_alpha = C_(Q_alpha)(Ltilde_alpha). The inherited quotient construction
supplies the projection, two-group kernel and common Sylow. The incident
parabolic identifications use the very same common representative.

Source: Meierfrankenfeld--Stellmacher (1993), (1.7), pp.847--848, and
(4.6.8), claim (3), p.906.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Quotient
open Escape.PairingControl.FirstPairing
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The literal finite local quotient by the fixed core. -/
abbrev Carrier (R : Subgroup M) := LocalQuotient (alpha R)

/-- The actual quotient image of an amalgam subgroup contained in G_alpha. -/
def image (A : Subgroup (FreeAmalgam R)) : Subgroup (Carrier R) :=
  quotientImage (alpha R) A

/-- Projection from M through its genuine incident-coordinate stabilizer isomorphism. -/
noncomputable def qmap (m : M) : M →* Carrier R :=
  (quotientMap (alpha R)).comp (stabilizerEquiv (R := R) m).toMonoidHom

theorem qmap_surjective (m : M) : Function.Surjective (qmap (R := R) m) :=
  (QuotientGroup.mk'_surjective _).comp (stabilizerEquiv m).surjective

theorem qmap_kernel (m : M) :
    (qmap (R := R) m).ker = pull m (fixedCore R (alpha R)) := by
  ext x
  change quotientMap (alpha R) (stabilizerEquiv m x) = 1 ↔ _
  rw [quotientMap, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rfl

/-- Pullback followed by the quotient is exactly the actual subgroup image. -/
theorem map_pull_qmap (m : M) (A : Subgroup (FreeAmalgam R)) :
    (pull m A).map (qmap m) = image A := by
  have he : (pull m A).map (stabilizerEquiv m).toMonoidHom =
      A.subgroupOf (stabilizer R (alpha R)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := (stabilizerEquiv m).surjective x
      exact ⟨y, hx, rfl⟩
  rw [qmap, ← map_map, he]
  rfl

variable [Finite M]

/-- The source projection expressed on the actual finite stabilizer. -/
noncomputable def stabilizerProjection (source : LocalSource L R) (m : M) :
    stabilizer R (alpha R) →* SL :=
  source.projection.comp (stabilizerEquiv m).symm.toMonoidHom

omit [Finite M] in
theorem stabilizerProjection_surjective (source : LocalSource L R) (m : M) :
    Function.Surjective (stabilizerProjection source m) :=
  source.projection_surjective.comp (stabilizerEquiv m).symm.surjective

theorem stabilizerProjection_kernel (source : LocalSource L R) (m : M) :
    (stabilizerProjection source m).ker =
      (Q R (alpha R)).subgroupOf (stabilizer R (alpha R)) := by
  have he : source.projection.ker.map (embedding R m) = Q R (alpha R) := by
    simpa only [pairingExtension_projection, pairing_core] using map_extension_core source m
  have hf (x : stabilizer R (alpha R)) :
      embedding R m ((stabilizerEquiv m).symm x) = x :=
    congrArg Subtype.val ((stabilizerEquiv m).apply_symm_apply x)
  ext x
  change source.projection ((stabilizerEquiv m).symm x) = 1 ↔ (x : FreeAmalgam R) ∈ Q R (alpha R)
  rw [← he]
  constructor
  · intro hx
    exact ⟨_, hx, hf x⟩
  · rintro ⟨y, hy, hxy⟩
    have h : (stabilizerEquiv m).symm x = y :=
      embedding_injective m ((hf x).trans hxy.symm)
    simpa only [h] using (show source.projection y = 1 from hy)

/-- The actual marked projection after dividing by D_alpha. -/
noncomputable def projection (source : LocalSource L R) (m : M) : Carrier R →* SL :=
  quotientProjection (alpha R) (stabilizerProjection source m)
    (stabilizerProjection_kernel source m)

@[simp] theorem projection_qmap (source : LocalSource L R) (m x : M) :
    projection source m (qmap m x) = source.projection x := by
  change source.projection ((stabilizerEquiv m).symm (stabilizerEquiv m x)) = _
  rw [MulEquiv.symm_apply_apply]

/-- The genuine Section 1 extension on G_alpha/D_alpha. -/
noncomputable def extension (source : LocalSource L R) (m : M) :
    RankOnePairing.Extension (M := Carrier R) :=
  quotientExtension source (alpha R) rfl (stabilizerProjection source m)
    (stabilizerProjection_surjective source m) (stabilizerProjection_kernel source m)
    source.flag source.weakBN

@[simp] theorem extension_projection (source : LocalSource L R) (m : M) :
    (extension source m).projection = projection source m := rfl

@[simp] theorem extension_flag (source : LocalSource L R) (m : M) :
    (extension source m).flag = source.flag := rfl

theorem extension_core (source : LocalSource L R) (m : M) :
    RankOnePairing.extensionCore (extension source m).projection = image (Q R (alpha R)) :=
  quotientExtension_core source _ rfl _ _ _ _ _

theorem extension_commonSylow (source : LocalSource L R) (m : M) :
    RankOnePairing.commonSylow (extension source m) =
      RankOnePairing.borelPreimage (projection source m) source.flag :=
  quotientExtension_commonSylow source _ rfl _ _ _ _ _

theorem extension_parabolic (source : LocalSource L R) (m : M) (j : Bool) :
    RankOnePairing.localParabolic (extension source m) j =
      parabolic (projection source m) source.flag j :=
  quotientExtension_parabolic source _ rfl _ _ _ _ _ j

/-- The same finite parabolic maps onto the marked parabolic in the fixed-core quotient. -/
theorem map_parabolic (source : LocalSource L R) (m : M) (j : Bool) :
    (RankOnePairing.localParabolic (Transport.extension source) j).map (qmap m) =
      RankOnePairing.localParabolic (extension source m) j := by
  rw [pairing_parabolic, extension_parabolic]
  have he : parabolic source.projection source.flag j =
      (parabolic (projection source m) source.flag j).comap (qmap m) := by
    ext x
    simp only [parabolic, mem_comap, projection_qmap]
  rw [he, map_comap_eq_self_of_surjective (qmap_surjective m)]

/-- The first full actor's literal quotient image. -/
theorem first_actor (source : LocalSource L R) (i : Bool) (d : M)
    (hd : flagIncident source i 1 d) :
    RankOnePairing.localParabolic (extension source (representative source i d hd)) i =
      image (flagParabolic source i) := by
  rw [← map_parabolic]
  conv_rhs => rw [← map_pull_qmap (representative source i d hd),
    ← map_first_actor source i d hd, pull_map]

/-- The second full actor's literal quotient image. -/
theorem second_actor (source : LocalSource L R) (i : Bool) (d : M)
    (hd : flagIncident source i 1 d) :
    RankOnePairing.localParabolic (extension source (representative source i d hd)) (!i) =
      image (localFlagActor source (!i) d) := by
  rw [← map_parabolic]
  conv_rhs => rw [← map_pull_qmap (representative source i d hd),
    ← map_second_actor source i d hd, pull_map]

/-- The central layer and pairing group are normal only in this finite quotient. -/
instance image_Z_normal : (image (Z R (alpha R))).Normal :=
  quotientImage_normal _ _ (Z_normalized R _)
instance image_V_normal : (image (V R (alpha R))).Normal :=
  quotientImage_normal _ _ (DistanceEight.V_normalized R _)

/-- The source pairing seed, global span, and fixed preimage in the finite quotient. -/
noncomputable def seed (source : LocalSource L R) (i : Bool) (d : M) : Subgroup (Carrier R) :=
  image (Pairing.seed source i d)

noncomputable def fixed (source : LocalSource L R) (i : Bool) (d : M)
    (hd : flagIncident source i 1 d) : Subgroup (Carrier R) :=
  RankOnePairing.fixedPreimage
    (RankOnePairing.component (projection source (representative source i d hd)) source.flag)
    (seed source i d) (image (Z R (alpha R)))

/-- Normality of the seed survives the actual quotient map. -/
theorem seed_normal (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d)
    (htriple : ⁅⁅V R (beta R), localFlagKernel source (!i) d⁆,
      localFlagResidual source (!i) d⁆ ≤ Z R (alpha R)) :
    ((seed source i d).subgroupOf
      (RankOnePairing.localParabolic (extension source (representative source i d hd)) (!i))).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  let m := representative source i d hd
  have h := pull_normalizes m _ _
    (Pairing.seed_normalized source geometry hlarge i hkernel d hd htriple)
  rw [← map_second_actor source i d hd, pull_map] at h
  have hh := (map_mono (f := qmap (R := R) m) h).trans (le_normalizer_map (qmap (R := R) m))
  rw [map_parabolic, map_pull_qmap] at hh
  exact hh

omit [Finite M] in
/-- Containment of actual local subgroups is preserved in the quotient. -/
theorem image_mono {A B : Subgroup (FreeAmalgam R)} (h : A ≤ B) : image A ≤ image B :=
  map_mono (comap_mono h)

omit [Finite M] in
/-- The image of an embedded finite subgroup has the literal quotient meaning. -/
theorem map_qmap (m : M) (A : Subgroup M) :
    A.map (qmap (R := R) m) = image (A.map (embedding R m)) := by
  rw [← map_pull_qmap m, pull_map]

omit [Finite M] in
/-- The seed contains the entire central natural image. -/
theorem Z_le_seed (source : LocalSource L R) (i : Bool) (d : M) :
    image (Z R (alpha R)) ≤ seed source i d := image_mono le_sup_left

/-- The seed lies in the extension core actually used by the pairing. -/
theorem seed_le_core (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) :
    seed source i d ≤ RankOnePairing.extensionCore
      (extension source (representative source i d hd)).projection := by
  rw [extension_core]
  exact image_mono (Pairing.seed_le_Q source geometry hlarge i hkernel d hd)

theorem radius_le_core (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (m : M) :
    image (V R (alpha R)) ≤ RankOnePairing.extensionCore (extension source m).projection := by
  rw [extension_core]
  exact image_mono (V_le_Q geometry hlarge _ rfl)

/-- Normal closure in the quotient is the image of the actual finite stabilizer span. -/
theorem generated_seed (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d) :
    RankOnePairing.generated (seed source i d) = image (Pairing.span source i d) := by
  let m := representative source i d hd
  have h := map_normalClosure (pull m (Pairing.seed source i d) : Set M)
    (qmap (R := R) m) (qmap_surjective m)
  rw [← coe_map, map_pull_qmap] at h
  change (RankOnePairing.generated (pull m (Pairing.seed source i d))).map (qmap m) =
    RankOnePairing.generated (seed source i d) at h
  rw [← h, map_qmap, map_generated_seed source geometry hlarge i hkernel d hd]

/-- The quotient component is the image of the actual global tilded residual. -/
theorem component_eq_image (source : LocalSource L R) (m : M) :
    RankOnePairing.component (projection source m) source.flag = image (Ltilde R (alpha R)) := by
  let := finite_stabilizer R (alpha R)
  have he : (Ltilde R (alpha R)).subgroupOf (stabilizer R (alpha R)) =
      pResidual 2 (stabilizer R (alpha R)) :=
    comap_map_eq_self_of_injective (stabilizer R (alpha R)).subtype_injective _
  rw [RankOnePairing.component, projection, rankOne_parabolic_generation _
    (quotientProjection_surjective _ _ (stabilizerProjection_surjective source m) _)
    (quotientProjection_kernel_isPGroup source _ rfl _ _),
    image, quotientImage, he, quotientMap,
    map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]

/-- The untilded local residual is the full actor in this actual two-group-kernel quotient. -/
theorem localResidual_eq_parabolic (source : LocalSource L R) (m : M) (j : Bool) :
    RankOnePairing.localResidual (RankOnePairing.localParabolic (extension source m) j) =
      RankOnePairing.localParabolic (extension source m) j := by
  rw [extension_parabolic, RankOnePairing.localResidual, projection,
    primeToResidual_parabolic_eq_top _
      (quotientProjection_surjective _ _ (stabilizerProjection_surjective source m) _)
      (quotientProjection_kernel_isPGroup source _ rfl _ _),
    ← MonoidHom.range_eq_map, range_subtype]

omit [Finite M] in
/-- Killing the genuine fixed core identifies the central image with its natural summand. -/
theorem image_Z_eq_U (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) :
    image (Z R (alpha R)) = image (U R (alpha R)) := by
  let F := Z R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R))
  have hF : F ≤ fixedCore R (alpha R) := by
    apply le_inf (inf_le_left.trans ?_) inf_le_right
    rw [← common.X_eq_Z _ rfl]
    exact omegaCenter_le _
  have hFS : F ≤ stabilizer R (alpha R) := inf_le_left.trans (Z_le_stabilizer R _)
  have hUS := (DistanceEight.U_le_Z R (alpha R)).trans (Z_le_stabilizer R (alpha R))
  have hk : image F = ⊥ := (quotientImage_eq_bot_iff _ _ hFS).mpr hF
  change ((Z R (alpha R)).subgroupOf (stabilizer R (alpha R))).map _ = _
  rw [common.decomposition, subgroupOf_sup hUS hFS, Subgroup.map_sup]
  change image (U R (alpha R)) ⊔ image F = _
  rw [hk, sup_bot_eq]

/-- Restrict the literal quotient map to the transported natural subgroup. -/
noncomputable def naturalImageMap (m : M) : pull m (U R (alpha R)) →* image (Z R (alpha R)) :=
  ((qmap (R := R) m).comp (pull m (U R (alpha R))).subtype).codRestrict _ (fun x => by
    rw [← map_pull_qmap m]
    exact mem_map_of_mem _ (DistanceEight.U_le_Z R _ x.property))

omit [Finite M] in
theorem naturalImageMap_bijective (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (m : M) :
    Function.Bijective (naturalImageMap (R := R) m) := by
  constructor
  · apply (naturalImageMap m).ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro x hx
    have hq : qmap m (x : M) = 1 := congrArg Subtype.val hx
    have hD : embedding R m (x : M) ∈ fixedCore R (alpha R) := by
      change (x : M) ∈ pull m (fixedCore R (alpha R))
      rw [← qmap_kernel]
      exact hq
    have he : embedding R m (x : M) = 1 := common.disjoint.le_bot
      ⟨x.property, DistanceEight.U_le_Z R _ x.property, hD.2⟩
    apply Subtype.ext
    exact embedding_injective m (he.trans (map_one (embedding R m)).symm)
  · intro x
    have hx : (x : Carrier R) ∈ image (U R (alpha R)) :=
      (image_Z_eq_U source geometry common) ▸ x.property
    rw [← map_pull_qmap m] at hx
    obtain ⟨y, hy, he⟩ := hx
    exact ⟨⟨y, hy⟩, Subtype.ext he⟩

/-- A concrete natural-group isomorphism onto the central quotient image. -/
noncomputable def naturalImageEquiv (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (m : M) :
    pull m (U R (alpha R)) ≃* image (Z R (alpha R)) :=
  MulEquiv.ofBijective (naturalImageMap m) (naturalImageMap_bijective source geometry common m)

/-- The natural central factor for (1.7), with the incident marking and actual action. -/
noncomputable def naturalZ (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (m : M) :
    RankOnePairing.NaturalFactor (projection source m) ⊤ (image (Z R (alpha R))) ⊥ := by
  let E := naturalImageEquiv source geometry common m
  let n := naturalCoordinates source geometry common m
  let c := E.symm.trans n.equivOfBot
  refine {
    marking := n.marking
    coordinates := c.toMonoidHom
    surjective := c.surjective
    kernel := ?_
    normalized := le_normalizer_of_normal
    action := ?_ }
  · rw [bot_subgroupOf]
    exact c.toMonoidHom.ker_eq_bot_iff.mpr c.injective
  · intro l _ x y hy
    obtain ⟨l₀, rfl⟩ := qmap_surjective m l
    let u := E.symm x
    let v := E.symm y
    have hu : l₀ * (u : M) * l₀⁻¹ ∈ pull m (U R (alpha R)) :=
      (mem_normalizer_iff.mp (n.normalized (mem_top l₀)) _).mp u.property
    let z : pull m (U R (alpha R)) := ⟨_, hu⟩
    have hz : E z = y := by
      apply Subtype.ext
      change qmap m (l₀ * (u : M) * l₀⁻¹) = (y : Carrier R)
      rw [map_mul, map_mul, map_inv]
      have hx : qmap m (u : M) = (x : Carrier R) :=
        congrArg Subtype.val (E.apply_symm_apply x)
      rw [hx]
      exact hy.symm
    have hv : (v : M) = l₀ * (u : M) * l₀⁻¹ :=
      congrArg Subtype.val (E.injective ((E.apply_symm_apply y).trans hz.symm))
    change (n.coordinates v).toAdd = _
    rw [projection_qmap]
    exact n.action l₀ (mem_top _) u v hv

/-- Vanishing of the actual quotient pairing gives exactly the required fixed-core bound. -/
theorem pairing_bound_of_quotient (source : LocalSource L R) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R)) (d : M)
    (hd : flagIncident source i 1 d)
    (h : ⁅⁅image (V R (alpha R)),
      RankOnePairing.component (projection source (representative source i d hd)) source.flag⁆,
      RankOnePairing.generated (seed source i d)⁆ = ⊥) :
    ⁅Vcirc R (alpha R), Pairing.span source i d⁆ ≤ fixedCore R (alpha R) := by
  have hV := geometry.V_local _ rfl hlarge
  have hL : Ltilde R (alpha R) ≤ stabilizer R (alpha R) := map_subtype_le _
  have hS := (Pairing.span_le_radius source geometry hlarge i hkernel d hd).trans hV
  rw [component_eq_image, generated_seed source geometry hlarge i hkernel d hd] at h
  change ⁅⁅quotientImage (alpha R) (V R (alpha R)), quotientImage (alpha R) (Ltilde R (alpha R))⁆,
    quotientImage (alpha R) (Pairing.span source i d)⁆ = ⊥ at h
  rw [← quotientImage_commutator _ _ _ hV hL] at h
  exact (quotient_commutator_eq_bot_iff _ _ _
    ((Subgroup.commutator_le_sup _ _).trans (sup_le hV hL)) hS).mp h

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.Pairing.Transport.Quotient
