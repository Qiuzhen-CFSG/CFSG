module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.InnerPlaneActors
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalSmallActor
/-!
# The critical index from a fixed-seed join escape

The large-actor proof needs only movement outside the critical commutator.
Its whole-Z bound then forces the moving-cover kernel to escape, producing
an invariant quadratic refinement. The orthogonal plane count excludes a
large actor over F4. A critical endpoint that does not normalize Y joined
with Z_alpha supplies exactly that movement, without an X-decomposition.
For Y in Q_alpha, centralization of the critical commutator is automatic.
The original small-actor theorem then makes both critical indices four.

Source: MS93 (3.3), first symplectic paragraph, p.867, and its application in
(3.4), p.868. This is an adequate specialized route preserving the earlier
source3.3 APIs and the full central cover attachment. No star-bound result
is used to prove the comparison.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open SourceComparison
variable {M : Type*} [Group M] {R : Subgroup M}
  {geometry : Geometry R} {a e : Vertex R}
/-- A critical endpoint failing to normalize the seed join forces movement
outside the critical commutator, without any X-layer comparison. -/
theorem critical_escape_of_seed_join_nonnormalization
    (path : CriticalPath R geometry a e) (Y : Subgroup (FreeAmalgam R))
    (hn : ¬ Z R e ≤ normalizer ((Y ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _)) :
    ¬ ⁅Z R e,Y⁆ ≤ ⁅Z R a,Z R e⁆ := by
  intro hc
  have hc' := hc.trans (critical_commutator_le_start_seed path)
  have hZn : Z R e ≤ normalizer (Z R a : Set (FreeAmalgam R)) := by
    apply (Z_le_stabilizer_of_dist_le e (geometry.exists_critical e path.end_color) ?_).trans
      (Z_normalized R a)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant e path.end_color]
  apply hn
  apply le_normalizer_iff.mpr
  intro z hz x hx
  have hmap : (Y ⊔ Z R a).map (MulAut.conj z).toMonoidHom ≤ Y ⊔ Z R a := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨y,hy,rfl⟩
      have hc := hc' (commutator_mem_commutator hz hy)
      have hh := (Y ⊔ Z R a).mul_mem (mem_sup_right hc) (mem_sup_left hy)
      simpa [commutatorElement_def,mul_assoc] using hh
    · exact (mem_normalizer_iff_map_conj_eq.mp (hZn hz)).le.trans le_sup_right
  exact hmap (mem_map_of_mem (MulAut.conj z).toMonoidHom hx)

theorem critical_large_actor_card_le_of_critical_escape
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    (Y : Subgroup (FreeAmalgam R))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range=U R e) (β : Z R a →* L (K := F))
    (hβ : ∀ z : Z R a, ∀ w : W,
      j (Multiplicative.ofAdd (σ (β z) w)) =
        (z:FreeAmalgam R)*j (Multiplicative.ofAdd w)*(z:FreeAmalgam R)⁻¹)
    (hker : ∀ w : W, p w=0 ↔
      j (Multiplicative.ofAdd w) ∈ centralizer (Ltilde R e : Set (FreeAmalgam R)))
    (hinner : Y ≤ Ltilde R e ⊔ centralizer (Z R e : Set (FreeAmalgam R)))
    (hcomm : ⁅Z R a,Y⁆ ≤ centralizer (Z R e : Set (FreeAmalgam R)))
    (hc : Y ≤ centralizer ((⁅Z R a,Z R e⁆ : Subgroup (FreeAmalgam R)) : Set _))
    (hbad : ¬ ⁅Z R e,Y⁆ ≤ ⁅Z R a,Z R e⁆)
    (hlarge : Nat.card F < Nat.card β.range) :
    Nat.card β.range ≤ 2*Nat.card F := by
  let α : Z R a →* Sp F := (commutator (Sp F)).subtype.comp β
  have hcard : Nat.card α.range=Nat.card β.range := by
    have he : α.range = β.range.map (commutator (Sp F)).subtype := MonoidHom.range_comp _ _
    rw [he]
    exact Nat.card_congr (Subgroup.equivMapOfInjective β.range _ Subtype.val_injective).toEquiv.symm
  obtain ⟨π,hπ⟩ := exists_embedded_projection (U R e) j hj hjr p.toLinearMap
  have hα (z : Z R a) (w : W) : p (σ (β z) w)=α z • p w := LinearMap.congr_fun (p.isIntertwining' (β z)) w
  obtain ⟨hP,hfixed,hcover⟩ := critical_displacement_plane_and_cover path hb σ j hj hjr β hβ
    p.toLinearMap hp.1 α hα π hπ (hcard.symm ▸ hlarge)
  have hact : ∀ (z : Z R a) (u : U R e),
      π ⟨z.val*u.val*z.val⁻¹,
        (mem_normalizer_iff.mp (critical_actor_normalizes_moving path z.property)
          u.val).mp u.property⟩ = Multiplicative.ofAdd (α z • (π u).toAdd) := by
    intro z u
    have hu : u.val ∈ j.range := by rw [hjr]; exact u.property
    obtain ⟨w,hw⟩ := hu
    have he : u=⟨j w,by rw [←hjr]; exact ⟨w,rfl⟩⟩ := Subtype.ext hw.symm
    subst u
    have hπw : π ⟨j w,by rw [←hjr]; exact ⟨w,rfl⟩⟩ = Multiplicative.ofAdd (p w.toAdd) := hπ w.toAdd
    rw [hπw]
    have hh := hβ z w.toAdd
    have hz : (⟨z.val*j w*z.val⁻¹,
        (mem_normalizer_iff.mp (critical_actor_normalizes_moving path z.property) (j w)).mp
          (by rw [←hjr]; exact ⟨w,rfl⟩)⟩ : U R e) =
        ⟨j (Multiplicative.ofAdd (σ (β z) w.toAdd)),by rw [←hjr]; exact ⟨_,rfl⟩⟩ :=
      Subtype.ext hh.symm
    rw [hz,hπ,toAdd_ofAdd]
    exact congrArg Multiplicative.ofAdd (hα z w.toAdd)
  have hπmul (w : Multiplicative W) (hw : j w ∈ U R e) :
      π ⟨j w,hw⟩=Multiplicative.ofAdd (p w.toAdd) := hπ w.toAdd
  have hk : π.ker.map (U R e).subtype = U R e ⊓ centralizer (Ltilde R e : Set _) := by
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      refine ⟨u.property,?_⟩
      have huj : u.val ∈ j.range := by rw [hjr]; exact u.property
      obtain ⟨w,hw⟩ := huj
      have he : u=⟨j w,by rw [←hjr]; exact ⟨w,rfl⟩⟩ := Subtype.ext hw.symm
      subst u
      apply (hker w.toAdd).mp
      change π ⟨j w,_⟩=1 at hu
      rw [hπmul] at hu
      exact ofAdd_eq_one.mp hu
    · rintro ⟨hu,hc⟩
      have huj : x ∈ j.range := by rwa [hjr]
      obtain ⟨w,rfl⟩ := huj
      refine ⟨⟨j w,hu⟩,?_,rfl⟩
      change π ⟨j w,hu⟩=1
      rw [hπmul]
      exact ofAdd_eq_one.mpr ((hker w.toAdd).mpr hc)
  have hbound := critical_top_layer_bound_of_inner_actors path Y π α hact
    (displacementSpace α.range) hfixed hcover hinner hcomm hc
  rw [hk] at hbound
  have hk' : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
      U R e ⊓ centralizer (Ltilde R e : Set (FreeAmalgam R)) := by
    ext x
    constructor
    · rintro ⟨w,hw,rfl⟩
      refine ⟨?_,(hker w.toAdd).mp hw⟩
      rw [←hjr]
      exact ⟨w,rfl⟩
    · rintro ⟨hx,hc⟩
      rw [←hjr] at hx
      obtain ⟨w,rfl⟩ := hx
      exact ⟨w,(hker w.toAdd).mpr hc,rfl⟩
  have hescape : ¬ p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j ≤ ⁅Z R a,Z R e⁆ := by
    rw [hk']
    intro hle
    exact hbad (hbound.trans (sup_le le_rfl hle))
  obtain ⟨c,hc'⟩ := embedded_cover_preserves_refinement_of_kernel_escape
    (⁅Z R a,Z R e⁆) (Z R a) σ p hp j β hβ
    (hjr.symm ▸ commutator_mono le_rfl (U_le_Z e)) hescape
  rw [←hcard]
  apply card_le_of_fixes_self_orthogonal_plane α.range (displacementSpace α.range) hP ?_ c ?_
  · rintro ⟨g,hg⟩ v hv
    have hf : v ∈ TwoLocalCover.fixedSpace α.range := by
      rw [←orthogonal_displacementSpace,hP]
      exact hv
    exact hf g hg
  · rintro ⟨g,⟨z,rfl⟩⟩ v
    exact hc' z v

variable {J V F : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  {z : Vertex R}
open ChapterB.QuasisimpleSource
theorem critical_large_actor_excluded_of_ambient_cover_of_critical_escape
    [FiniteDimensional (ZMod 2) V]
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (Y : Subgroup (FreeAmalgam R)) (hYZ : Y ≤ stabilizer R z)
    (hF : Nat.card F = 4)
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
    (hbad : ¬ ⁅Z R z,Y⁆ ≤ ⁅Z R a,Z R z⁆)
    (hlarge : 16 ≤ Nat.card β.range) : False := by
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
      path hb σ j hj hjr β hβact p.toLinearMap hp.1 α hα π hπ (by omega)
  have hfix (x : Z R a) (v : Vector F) (hv : v ∈ displacementSpace α.range) :
      MovedSection.ambientAction s e
        (κ ⟨x,Z_le_stabilizer_of_dist_le a
          (geometry.exists_critical a path.start_color) path.critical.1.le x.property⟩) v=v := by
    rw [←hβ, MovedSection.ambientAction_component,e.groupEquiv.apply_symm_apply]
    have hv' : v ∈ TwoLocalCover.fixedSpace α.range := by
      rw [←orthogonal_displacementSpace,hP]
      exact hv
    exact hv' (α x) ⟨x,rfl⟩
  obtain ⟨hinner,hcomm⟩ := critical_inner_plane_actors path Y hYZ s e (by omega) hcent
    j hj hjr κ hk hB hconj π hπ (displacementSpace α.range) hP hcover hfix hc
  have hbound := critical_large_actor_card_le_of_critical_escape
    path hb Y σ p hp j hj hjr β hβact hker hinner hcomm hc hbad (by omega)
  omega


end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open ChapterB.QuasisimpleSource MSCentralOrbit SourceComparison
open Representation.SymplecticFourOrthogonalCover
open Theory.GroupTheory
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]
theorem original_large_critical_index_lt_sixteen_of_critical_escape
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (Y : Subgroup (FreeAmalgam R))
    (hYZ : Y ≤ stabilizer R z)
    (hcentral : Y ≤ centralizer ((⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set _))
    (hbad : ¬ ⁅Z R z,Y⁆ ≤ ⁅Z R a,Z R z⁆) :
    (Q R z).relIndex (Z R a) < 16 := by
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) ((pResidual 2 H).map q)
  obtain ⟨F,hF,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hconj,hproj,hker⟩ :=
    ambient_initial_cover_at_vertex R hms hp hne hQR hself hfaith q hq hcore
      hc hC hsq path.end_color
  have hFcard : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  have hAZ : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  let δ : Z R a →* J := κ.comp (inclusion hAZ)
  have hcard : Nat.card δ.range = (Q R z).relIndex (Z R a) :=
    quotient_image_card _ _ _ hAZ κ hκQ
  apply Nat.lt_of_not_ge
  intro hlarge
  have hδ : ∀ x : Z R a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd v) * (x : FreeAmalgam R)⁻¹ :=
    fun x v => hconj (inclusion hAZ x) v
  obtain ⟨β,hβcard,hβmark,_⟩ := critical_inner_model_actor path hb hFcard s e he hC
    j hj hjr δ hδ (by omega)
  exact critical_large_actor_excluded_of_ambient_cover_of_critical_escape path hb Y hYZ hFcard s e he hC
    j hj hjr κ hκC hκL hconj β hβmark hker hcentral hbad (by omega)



theorem original_critical_indices_eq_four_of_seed_join_nonnormalization
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (Y : Subgroup (FreeAmalgam R))
    (hYZ : Y ≤ stabilizer R z)
    (hcentral : Y ≤ centralizer ((⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set _))
    (hn : ¬ Z R z ≤ normalizer ((Y ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _)) :
    (Q R z).relIndex (Z R a)=4 ∧ (Q R a).relIndex (Z R z)=4 := by
  apply SourceComparison.original_small_critical_indices_eq_four R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path hb
  exact original_large_critical_index_lt_sixteen_of_critical_escape R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path hb Y hYZ hcentral
    (critical_escape_of_seed_join_nonnormalization path Y hn)

theorem original_critical_indices_eq_four_of_core_seed
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (Y : Subgroup (FreeAmalgam R))
    (hYZ : Y ≤ stabilizer R z)
    (hYQ : Y ≤ Q R a)
    (hn : ¬ Z R z ≤ normalizer ((Y ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _)) :
    (Q R z).relIndex (Z R a)=4 ∧ (Q R a).relIndex (Z R z)=4 := by
  have hcentral : Y ≤ centralizer ((⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set _) :=
    (hYQ.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a path.start_color)))).trans
      (centralizer_le (CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path))
  exact original_critical_indices_eq_four_of_seed_join_nonnormalization R hms hp hne hQR
    hself hfaith q hq hcore hc hC hsq path hb Y hYZ hcentral hn

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
