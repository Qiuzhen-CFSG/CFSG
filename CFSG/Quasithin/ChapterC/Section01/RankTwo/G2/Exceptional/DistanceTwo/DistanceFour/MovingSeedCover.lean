module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.DistanceTwo.DistanceFour.MidpointMovement
public import Theory.Representation.BinaryConjugationSection.CentralKernel
public import Theory.Representation.BinaryConjugationSection.Coinvariants
public import Theory.Representation.G2OrthogonalCover.PointStabilizers
public import Theory.Representation.G2NaturalExtensions.FixedSpaces

/-!
Adapted from the checked Chapter15 MarkedMS.G2Reconstruction proof to the
exceptional MS2(b) input. Only the two-group and core-containment consequences
of MS2 are used; the original SmallMSPair interface is unchanged.

# The original moving seed as a trace-zero quotient

The endpoint actor is full G₂(2): its image contains the derived subgroup
and a critical offender with a short root outside the derived subgroup.
Conjugation on U descends along that same actor, since its kernel centralizes
X = Z. Residual generation and the original endpoint projection make U a
central cover of the natural module. Universality gives a surjective
trace-zero cover; uniqueness extends its equivariance to the full actor.
The octonion norm then lifts natural fixation to actual fixation on U.

These are the moving-module and fixed-lifting steps used in the last
paragraph of MS93 (3.8), printed p.879. The covering model retains the
ATLAS attribution in LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour
open ChapterC BinaryMS.MS93 Comparison Comparison.CriticalImage
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "T" => R.subgroupOf (L ⊔ R)
variable (h : Pair KnownSimple.IsKnownSimple L R)
  (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2)))

include h e in
/-- The literal endpoint actor contains the derived group and an offender
with a short root outside it, hence maps onto the full G₂(2). -/
theorem seed_actor_surjective (a : Vertex T) (ha : color T a = false)
    (d : EndpointModel T a) : Function.Surjective d.actor := by
  obtain ⟨z,hc⟩ := criticalPair_exists T a ((geometry h).exists_critical a ha)
  have hz := critical_endpoint_color T a ha _ hc
  have hrev := critical_reverse T (geometry h) (edgeCentralizer h e) a ha (by
    rw [(geometry h).distance_constant a ha]; exact (positive_even h e).1) z hz hc
  obtain ⟨dz⟩ := endpointModel_knownSimple h e hz
  have hoff := critical_image_offender (geometry h) (edgeCentralizer h e)
    z a hz (positive_even h e).1 hrev dz d
  have hnat := hoff.map_equivariant rho (Atlas.G2.Natural.action (ZMod 2))
    (MonoidHom.id _) Function.injective_id
    (Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2)).symm
    (fun g v => (Atlas.G2.Restricted.NaturalCoordinates.repEquiv (ZMod 2)).symm.isIntertwining g v)
  rw [map_id] at hnat
  obtain ⟨g,_,hg⟩ := Atlas.G2.NaturalOffenders.natural_offender_rootPair
    (n := 1) (by norm_num) (by decide) _ hnat
  have hout : g * Atlas.G2.rootC 1 * g⁻¹ ∉ commutator (Atlas.G2.Model (ZMod 2)) := by
    intro hgD
    have hc := (inferInstance : (commutator (Atlas.G2.Model (ZMod 2))).Normal).conj_mem' _ hgD g
    apply Atlas.G2.Natural.BinaryNormalizer.rootC_not_mem_derived
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hc
  have htop : d.actor.range = ⊤ := Atlas.G2.Natural.BinaryNormalizer.eq_top_of_derived_le
    (by
      change commutator (Atlas.G2.Model (ZMod 2)) ≤ _
      rw [←d.actor_residual]
      exact map_le_range _ _)
    (map_le_range _ _ hg) hout
  exact MonoidHom.range_eq_top.mp htop

include h e in
/-- The actual moving seed covers the entire natural quotient through the
original endpoint projection. -/
theorem moving_seed_projection_top (a : Vertex T) (ha : color T a = false)
    (d : EndpointModel T a) : ((U T a).subgroupOf (Z T a)).map d.projection = ⊤ := by
  apply seed_projection_surjective_of_residual_generated a d _ (U_le_Z a)
    ((geometry h).U_full_commutation (positive_even h e).1 a ha)
  intro hzero
  obtain ⟨z,hc⟩ := criticalPair_exists T a ((geometry h).exists_critical a ha)
  have hc0 := (critical_commutator_le_start_moving h e a z ha hc).trans_eq hzero
  have hc0' : ⁅Z T a,Z T z⁆ = ⊥ := bot_unique hc0
  have hcard := critical_commutator_card_ge_eight h e a z ha hc
  simp [hc0'] at hcard

include h e in
/-- A surjective trace-zero cover of the original moving seed, intertwining
its full actor and retaining its specified natural projection. -/
theorem moving_seed_cover (a : Vertex T) (ha : color T a = false)
    (d : EndpointModel T a) :
    ∃ f : Multiplicative (Atlas.G2.Natural.TraceZero (ZMod 2)) →* U T a,
      Function.Surjective f ∧
      (∀ (s : stabilizer T a) w,
        (f (Multiplicative.ofAdd (Atlas.G2.Natural.traceZeroAction (ZMod 2) (d.actor s) w)) : FreeAmalgam T) =
          s.val * (f (Multiplicative.ofAdd w) : FreeAmalgam T) * s.val⁻¹) ∧
      ∀ w, d.projection ⟨f (Multiplicative.ofAdd w), U_le_Z a (f (Multiplicative.ofAdd w)).property⟩ =
        Multiplicative.ofAdd (Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2)
          (Atlas.G2.Natural.mk (ZMod 2) w)) := by
  let := (geometry h).Z_elementary (positive_even h e).1 a ha
  let : IsElementaryAbelian 2 (U T a) := IsElementaryAbelian.of_injective
    (inclusion (U_le_Z a)) (inclusion_injective _)
  let := finite_Z T a
  let : Finite (U T a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  have hq := seed_actor_surjective h e a ha d
  have hker (s : stabilizer T a) (hs : s ∈ d.actor.ker) :
      s.val ∈ centralizer (U T a : Set (FreeAmalgam T)) := by
    have hsQ : s.val ∈ Q T a := by
      rw [←d.actor_kernel]
      exact mem_map_of_mem (stabilizer T a).subtype hs
    apply Subgroup.centralizer_le (show U T a ≤ X T a from by
      rw [omegaCenter_eq_seed h e a ha]
      exact U_le_Z a)
    exact Q_le_centralizer_X T a hsQ
  obtain ⟨σ,c,hc⟩ := BinaryConjugationSection.exists_of_central_kernel
    (stabilizer T a) (U T a) ((U_le_Z a).trans (Z_le_stabilizer T a))
    (U_normalized a) d.actor hq hker
  have hσ (s : stabilizer T a) (w : Additive (U T a)) :
      ((σ (d.actor s) w).toMul : FreeAmalgam T) = s.val * w.toMul.val * s.val⁻¹ := by
    have hh := c.equivariant s w.toMul
    have hh' := congrArg Multiplicative.toAdd hh
    rw [hc,hc] at hh'
    exact (congrArg (fun x : Additive (U T a) => x.toMul.val) hh').symm
  let p₀ : Additive (U T a) →ₗ[ZMod 2] NaturalSpace :=
    (MonoidHom.toAdditiveLeft (d.projection.comp (inclusion (U_le_Z a)))).toZModLinearMap 2
  let E := Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2)
  let p := E.symm.toLinearMap.comp p₀
  have hp₀ : Function.Surjective p₀ := by
    intro v
    obtain ⟨x,hx,hxv⟩ := (show Multiplicative.ofAdd v ∈
        ((U T a).subgroupOf (Z T a)).map d.projection from
      (moving_seed_projection_top h e a ha d).symm ▸ mem_top _)
    exact ⟨Additive.ofMul ⟨x.val,hx⟩,congrArg Multiplicative.toAdd hxv⟩
  have hp : Function.Surjective p := E.symm.surjective.comp hp₀
  have he₀ (s : stabilizer T a) (w : Additive (U T a)) :
      p₀ (σ (d.actor s) w) = rho (d.actor s) (p₀ w) := by
    have hh := d.intertwines s (inclusion (U_le_Z a) w.toMul)
    have hx : inclusion (U_le_Z a) (σ (d.actor s) w).toMul =
        ⟨s.val*w.toMul.val*s.val⁻¹,
          (mem_normalizer_iff.mp (Z_normalized T a s.property) w.toMul.val).mp
            (U_le_Z a w.toMul.property)⟩ := Subtype.ext (hσ s w)
    change (d.projection (inclusion _ _)).toAdd = _
    rw [hx]
    exact congrArg Multiplicative.toAdd hh
  have he (g : Atlas.G2.Model (ZMod 2)) (w : Additive (U T a)) :
      p (σ g w) = Atlas.G2.Natural.action (ZMod 2) g (p w) := by
    obtain ⟨s,rfl⟩ := hq g
    change E.symm (p₀ (σ (d.actor s) w)) = _
    rw [he₀]
    exact (Atlas.G2.Restricted.NaturalCoordinates.repEquiv (ZMod 2)).symm.isIntertwining _ _
  let D := commutator (Atlas.G2.Model (ZMod 2))
  have hk : p.ker ≤ Representation.OneCohomology.fixed (σ.comp D.subtype) := by
    intro w hw g
    have hw0 : p₀ w = 0 := E.symm.injective (show E.symm (p₀ w) = E.symm 0 from hw.trans (map_zero _).symm)
    have hwfix : w.toMul.val ∈ centralizer (Ltilde T a : Set (FreeAmalgam T)) := by
      have hm : w.toMul.val ∈ d.projection.ker.map (Z T a).subtype :=
        ⟨inclusion (U_le_Z a) w.toMul,congrArg Multiplicative.ofAdd hw0,rfl⟩
      rw [d.projection_kernel] at hm
      exact hm.2
    obtain ⟨s,hs,hsg⟩ := (show g.val ∈ ((Ltilde T a).subgroupOf (stabilizer T a)).map d.actor from
      d.actor_residual.symm ▸ g.property)
    change σ g.val w = w
    rw [←hsg]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hσ,hwfix s.val hs,mul_inv_cancel_right]
  let r : Ltilde T a →* D :=
    (d.actor.comp (inclusion (Ltilde_le_stabilizer a))).codRestrict D (by
      intro s
      change d.actor (inclusion (Ltilde_le_stabilizer a) s) ∈ commutator (Atlas.G2.Model (ZMod 2))
      rw [←d.actor_residual]
      exact mem_map_of_mem d.actor s.property)
  have hgen : Coinvariants.ker (σ.comp D.subtype) = ⊤ := by
    apply c.coinvariants_eq_top_of_group_generation (Ltilde T a) (Ltilde_le_stabilizer a)
      (σ.comp D.subtype) r (fun _ _ => rfl)
    rw [sup_bot_eq,commutator_comm,(geometry h).U_full_commutation (positive_even h e).1 a ha]
  let P : Representation.IntertwiningMap (σ.comp D.subtype) (Atlas.G2.Natural.OrthogonalCover.binaryNatural (ZMod 2)) :=
    p.intertwiningMap_of_isIntertwiningMap _ _ (fun g v => he g.val v)
  obtain ⟨f,hf,hover⟩ := Atlas.G2.Natural.OrthogonalCover.exists_quotient (ZMod 2) P ⟨hp,hk,hgen⟩
  have hwhole := Representation.OneCohomology.CentralCoverOriginalAction.quotient_original_equivariant D
    (η := Atlas.G2.Natural.action (ZMod 2)) (ζ := Atlas.G2.Natural.traceZeroAction (ZMod 2))
    (τ := σ) (Atlas.G2.Natural.mk (ZMod 2)) p f.toLinearMap (fun _ _ => rfl) he hk
    (Atlas.G2.Natural.OrthogonalCover.commutator_eq_top (ZMod 2))
    (fun g w => LinearMap.congr_fun (f.isIntertwining' g) w) hover
  let F : Multiplicative (Atlas.G2.Natural.TraceZero (ZMod 2)) →* U T a := {
    toFun := fun w => (f w.toAdd).toMul
    map_one' := by
      change (f 0).toMul = 1
      rw [map_zero]
      rfl
    map_mul' := by
      intro x y
      change (f (x.toAdd + y.toAdd)).toMul = _
      rw [map_add]
      rfl }
  refine ⟨F,hf,?_,?_⟩
  · intro s w
    change ((f (Atlas.G2.Natural.traceZeroAction (ZMod 2) (d.actor s) w)).toMul : FreeAmalgam T) = _
    exact (congrArg (fun v : Additive (U T a) => v.toMul.val) (hwhole (d.actor s) w)).trans (hσ s (f w))
  · intro w
    apply Multiplicative.toAdd.injective
    change p₀ (f w) = E (Atlas.G2.Natural.mk (ZMod 2) w)
    exact E.symm.injective (by rw [E.symm_apply_apply]; exact hover w)

include h e in
/-- Natural fixation lifts to the original moving seed: the octonion norm
kills the possible scalar displacement in its trace-zero cover. -/
theorem moving_seed_fixed_of_projection_fixed
    (a : Vertex T) (ha : color T a = false) (d : EndpointModel T a)
    (s : stabilizer T a) (x : U T a)
    (hx : rho (d.actor s) (d.projection (inclusion (U_le_Z a) x)).toAdd =
      (d.projection (inclusion (U_le_Z a) x)).toAdd) :
    s.val*x.val*s.val⁻¹ = x.val := by
  obtain ⟨f,hf,he,hp⟩ := moving_seed_cover h e a ha d
  obtain ⟨w,rfl⟩ := hf x
  have hpw := congrArg Multiplicative.toAdd (hp w.toAdd)
  let E := Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2)
  change (d.projection (inclusion (U_le_Z a) (f w))).toAdd = E (Atlas.G2.Natural.mk (ZMod 2) w.toAdd) at hpw
  have hn : Atlas.G2.Natural.action (ZMod 2) (d.actor s)
      (Atlas.G2.Natural.mk (ZMod 2) w.toAdd) = Atlas.G2.Natural.mk (ZMod 2) w.toAdd := by
    apply E.injective
    calc
      E (Atlas.G2.Natural.action (ZMod 2) (d.actor s) (Atlas.G2.Natural.mk (ZMod 2) w.toAdd)) =
          rho (d.actor s) (E (Atlas.G2.Natural.mk (ZMod 2) w.toAdd)) :=
        (Atlas.G2.Restricted.NaturalCoordinates.repEquiv (ZMod 2)).isIntertwining _ _
      _ = _ := by
        rw [←hpw]
        exact hx
  have hz := Atlas.G2.Natural.Extensions.traceZero_fixed_of_natural_fixed (d.actor s) w.toAdd hn
  exact (he s w.toAdd).symm.trans (congrArg (fun v => (f (Multiplicative.ofAdd v) : FreeAmalgam T)) hz)

end CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction.DistanceTwo.DistanceFour
