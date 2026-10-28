module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.ReciprocalActors
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.InnerPlaneActors
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.CoreReconstruction.OriginalSecondary
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.CoreReconstruction.RootCommutator

/-!
# The non-Frattini comparison at distance two

If the whole core escapes Phi(Q)X, its critical commutator fails the source
comparison in (3.3). The inner critical action constructed at the original
field degree has order below q squared: otherwise its invariant quadratic
refinement bounds its order by 2q, a contradiction for q > 2. Reciprocal
comparison therefore gives root images of order q at both endpoints.

The maximal secondary seed then lies in the opposite Q. Its actual local
conjugate orbit stays in Q, and its commutator and Frattini image lie in Z.
These are the source inputs to the remaining secondary-orbit contradiction;
no fixed central attachment is assumed trivial or removed.

Source: MS93 (3.3), (3.6), printed pp.867, 870--871. This module does not
assert the whole-core bound or the field restriction of (3.7).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource
open Representation.SymplecticFourOrthogonalCover
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction
section Large
variable {M J V : Type*} [Group M] [Group J] [AddCommGroup V] [Module (ZMod 2) V]
  {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
  {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
  {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
private theorem large_actor_excluded
    [FiniteDimensional (ZMod 2) V]
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (Y : Subgroup (FreeAmalgam R)) (hYZ : Y ≤ stabilizer R z)
    (hF : 2 < Nat.card F)
    (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hcent : centralizer (B : Set J) = ⊥)
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R)
    (hj : Function.Injective j) (hjr : j.range = U R z)
    (κ : stabilizer R z →* J)
    (hk : κ.ker.map (stabilizer R z).subtype = C R z)
    (hB : ((Ltilde R z).subgroupOf (stabilizer R z)).map κ = B)
    (hconj : ∀ (g : stabilizer R z) (v : s.space.toSubmodule),
      j (Multiplicative.ofAdd (s.space.toRepresentation (κ g) v)) =
        (g : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(g : FreeAmalgam R)⁻¹)
    (β : Z R a →* L (K := F))
    (hβ : ∀ x : Z R a,
      (e.groupEquiv.symm (β x) : J) = κ ⟨x,Z_le_stabilizer_of_dist_le a
        (geometry.exists_critical a path.start_color) path.critical.1.le x.property⟩)
    (hker : ∀ w : s.space.toSubmodule, MovedSection.coverProjection s e w=0 ↔
      j (Multiplicative.ofAdd w) ∈ centralizer (Ltilde R z : Set (FreeAmalgam R)))
    (hc : Y ≤ centralizer ((⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set _))
    (hbad : ¬ ⁅Z R z,Y⁆ ≤ ⁅X R a,X R z⁆ ⊔ ⁅X R a ⊓ Q R z,Y⁆)
    (hlarge : Nat.card F ^ 2 ≤ Nat.card β.range) : False := by
  have hgt : Nat.card F < Nat.card β.range := by nlinarith
  let α : Z R a →* Sp F := (commutator (Sp F)).subtype.comp β
  let p := MovedSection.coverProjection s e
  let σ := MovedSection.coverAction s e
  have hβact (x : Z R a) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ (β x) w)) =
        (x : FreeAmalgam R)*j (Multiplicative.ofAdd w)*(x : FreeAmalgam R)⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation (e.groupEquiv.symm (β x)) w)) = _
    rw [hβ]
    exact hconj _ w
  have hcard : Nat.card α.range=Nat.card β.range := by
    have he : α.range = β.range.map (commutator (Sp F)).subtype := MonoidHom.range_comp _ _
    rw [he]
    exact Nat.card_congr (Subgroup.equivMapOfInjective β.range _ Subtype.val_injective).toEquiv.symm
  obtain ⟨π,hπ⟩ := exists_embedded_projection (U R z) j hj hjr p.toLinearMap
  have hα (x : Z R a) (w : s.space.toSubmodule) : p (σ (β x) w)=α x • p w :=
    LinearMap.congr_fun (p.isIntertwining' (β x)) w
  obtain ⟨hP,_,hcover⟩ :=
    CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_displacement_plane_and_cover
      path hb σ j hj hjr β hβact p.toLinearMap hp.1 α hα π hπ (hcard.symm ▸ hgt)
  have hfix (x : Z R a) (v : Vector F) (hv : v ∈ displacementSpace α.range) :
      MovedSection.ambientAction s e
        (κ ⟨x,Z_le_stabilizer_of_dist_le a
          (geometry.exists_critical a path.start_color) path.critical.1.le x.property⟩) v=v := by
    rw [←hβ, MovedSection.ambientAction_component,e.groupEquiv.apply_symm_apply]
    have hv' : v ∈ TwoLocalCover.fixedSpace α.range := by
      rw [←orthogonal_displacementSpace,hP]
      exact hv
    exact hv' (α x) ⟨x,rfl⟩
  obtain ⟨hinner,hcomm⟩ := critical_inner_plane_actors path Y hYZ s e hF hcent
    j hj hjr κ hk hB hconj π hπ (displacementSpace α.range) hP hcover hfix hc
  have hbound := CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_large_actor_card_le
    path hb Y σ p hp j hj hjr β hβact hker hinner hcomm hc hbad hgt
  nlinarith


end Large
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R) {g : Geometry d.radical}
  {a z : Vertex d.radical}

include h

/-- The original failed comparison bounds the critical index below q squared.
The natural cover and inner actors are constructed from the input, and the
plane-fixer argument supplies the auxiliary actor hypotheses. -/
theorem replacement_critical_index_lt_field_sq_of_bad
    (path : CriticalPath d.radical g a z) (hb : 0 < g.b d.radical)
    (Y : Subgroup (FreeAmalgam d.radical)) (hY : Y ≤ stabilizer d.radical z)
    (hc : Y ≤ centralizer ((⁅Z d.radical a,Z d.radical z⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set _))
    (hbad : ¬ ⁅Z d.radical z,Y⁆ ≤ ⁅X d.radical a,X d.radical z⁆ ⊔
      ⁅X d.radical a ⊓ Q d.radical z,Y⁆) :
    (Q d.radical z).relIndex (Z d.radical a) < (2^n)^2 := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hQ,hC,hK,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.end_color
  have hfield : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hfield]
    exact lt_of_lt_of_le (by decide : 2 < 2^2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hAZ : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  let δ := κ.comp (inclusion hAZ)
  have hind : Nat.card δ.range = (Q d.radical z).relIndex (Z d.radical a) :=
    quotient_image_card _ _ _ hAZ κ hQ
  have houter : Nat.card (E.Carrier ≃+* E.Carrier) < Nat.card δ.range := by
    rw [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hfield,hind]
    exact (show n < 2^n from Nat.lt_two_pow_self).trans_le
      (replacement_critical_indices_ge_field h d path hb).1
  have hδ : ∀ x : Z d.radical a, ∀ w : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) w)) =
        (x : FreeAmalgam d.radical) * j (Multiplicative.ofAdd w) *
          (x : FreeAmalgam d.radical)⁻¹ := fun x w => hconj (inclusion hAZ x) w
  obtain ⟨β,hβ,hm,_⟩ := critical_inner_model_actor_of_field_bound path hb hcard s e he
    (replacement_component_image_structure h d).2.2.2.2 j hj hjr δ hδ houter
  by_contra hlarge
  exact large_actor_excluded path hb Y hY hcard s e he
    (replacement_component_image_structure h d).2.2.2.2
    j hj hjr κ hC hK hconj β hm hker hc hbad (by rw [hβ,hind,hfield]; omega)

/-- Failure of the whole-core bound forces the small critical-image branch
of MS93 (3.3), for the original field and the literal replacement kernels. -/
theorem replacement_critical_index_lt_field_sq_of_nonfrattini
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    (Q d.radical z).relIndex (Z d.radical a) < (2^n)^2 := by
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hQ,hC,hK,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.start_color
  let C := replacementComponent d
  let : (((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ).Normal := by
    rw [hK]
    exact replacementComponent_normal h d
  let : IsSimpleGroup (((Ltilde d.radical a).subgroupOf
      (stabilizer d.radical a)).map κ) := by
    rw [hK]
    exact (replacement_component_image_structure h d).2.2.1
  let : IsSimpleGroup C := (replacement_component_image_structure h d).2.2.1
  let : IsQuasisimple C := (replacement_component_image_structure h d).2.2.2.1
  have hna : ¬ IsMulCommutative (((Ltilde d.radical a).subgroupOf
      (stabilizer d.radical a)).map κ) := by
    rw [hK]
    exact Group.IsPerfect.not_isMulCommutative C
  have hcent : centralizer (((Ltilde d.radical a).subgroupOf
      (stabilizer d.radical a)).map κ : Set (d.overgroup ⧸ pCore 2 d.overgroup)) = ⊥ := by
    rw [hK]
    exact (replacement_component_image_structure h d).2.2.2.2
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  have hbad := critical_bad_comparison_of_nonfrattini path hb hedge
    (Q_isPGroup d.radical (replacement_isPGroup h d) (replacement_core_le h d) a path.start_color)
    κ hκ hQ hna hcent hlarge
  have hd : (cosetGraph d.radical).dist a z = 2 :=
    path.critical.1.trans ((g.distance_constant a path.start_color).trans hb)
  have hZa : Z d.radical a ≤ X d.radical a := g.omega_bound a path.start_color (by
    rw [g.distance_constant a path.start_color]
    change 0 < g.b d.radical
    omega)
  have hcomm : ⁅Z d.radical a,Z d.radical z⁆ ≤ X d.radical a :=
    (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path).trans hZa
  exact replacement_critical_index_lt_field_sq_of_bad h d path (by omega)
    (Q d.radical a) (Q_le_stabilizer_of_dist_two d.radical a z path.start_color hd)
    ((Q_le_centralizer_X d.radical a).trans (centralizer_le hcomm)) hbad

/-- The non-Frattini branch has literal critical root actions of order q on
both endpoints. Their full fixed kernels have been retained in the covers. -/
theorem replacement_nonfrattini_root_actions
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    ∃ e : CriticalNaturalAction d.radical a z n,
      ∃ f : CriticalNaturalAction d.radical z a n,
        (Q d.radical z).relIndex (Z d.radical a) = 2^n ∧
        (Q d.radical a).relIndex (Z d.radical z) = 2^n ∧
        Module.finrank e.field.Carrier (displacementSpace e.actor.range) = 1 ∧
        Module.finrank f.field.Carrier (displacementSpace f.actor.range) = 1 :=
  replacement_critical_root_actions_of_small h d path (by omega)
    (replacement_critical_index_lt_field_sq_of_nonfrattini h d path hb hlarge)

/-- In the failed whole-core branch, the maximal source seed is contained
in the original opposite kernel. This uses the actual quotient component. -/
theorem replacement_secondary_seed_le_kernel
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    {t : Vertex d.radical} (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    Sp4Four.secondarySeed d.radical a t z ≤ Q d.radical a := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (pResidual 2 d.overgroup).map q
  have hC : C = replacementComponent d := by
    dsimp only [C]
    rw [replacement_residual h d]
    rfl
  let : C.Normal := hC.symm ▸ replacementComponent_normal h d
  let : IsSimpleGroup C := hC.symm ▸ (replacement_component_image_structure h d).2.2.1
  let : IsQuasisimple C := hC.symm ▸ (replacement_component_image_structure h d).2.2.2.1
  have hc : centralizer (C : Set (d.overgroup ⧸ pCore 2 d.overgroup)) = ⊥ := by
    rw [hC]
    exact (replacement_component_image_structure h d).2.2.2.2
  exact original_secondarySeed_le_kernel d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) hc path hb hat hzt hlarge

/-- The literal secondary orbit stays in Q; its commutator and Frattini image
stay in Z. No central fixed attachment is discarded in these bounds. -/
theorem replacement_secondary_orbit_bounds
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    {t : Vertex d.radical} (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let Y := Sp4Four.secondarySeed d.radical a t z
    let A := Sp4Four.secondaryOrbit d.radical a Y
    A ≤ Q d.radical a ∧ ⁅A,Q d.radical a⁆ ≤ Z d.radical a ∧
      (frattini A).map A.subtype ≤ Z d.radical a := by
  let Y := Sp4Four.secondarySeed d.radical a t z
  let A := Sp4Four.secondaryOrbit d.radical a Y
  have hYQ := replacement_secondary_seed_le_kernel h d path hb hat hzt hlarge
  have hpos : 0 < g.b d.radical := by omega
  have hcomm : ⁅A,Q d.radical a⁆ ≤ Z d.radical a :=
    conjugatesIn_commutator_le Y (stabilizer d.radical a) (Q d.radical a) (Z d.radical a)
      hYQ (Q_normalized d.radical a) (Z_normalized d.radical a)
      (le_trans (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1)
        (Z_normalized d.radical a))
      ((Sp4Four.secondarySeed_greatest d.radical g path.end_color hzt hpos).2.1.trans
        (Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat))
  exact ⟨Sp4Four.conjugatesIn_le_of_normalized Y _ _ hYQ (Q_normalized d.radical a),hcomm,
    (Sp4Four.secondary_orbit_frattini_le d.radical g (replacement_isPGroup h d)
      (replacement_core_le h d) path.start_color path.end_color hpos Y
      (Sp4Four.secondarySeed_le d.radical a t z) hYQ).trans hcomm⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
