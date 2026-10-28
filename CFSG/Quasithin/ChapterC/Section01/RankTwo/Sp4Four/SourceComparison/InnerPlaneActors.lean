module
public import Theory.Representation.SymplecticNaturalNormalizer.FixedPlaneInner
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.CriticalImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.LargeActor

/-!
# The original inner-plane actors in the symplectic comparison

Centralizing the original critical commutator fixes its covered natural
plane in the full marked ambient action. The plane-fixer theorem places the
actor in the original component modulo its exact kernel and makes its image
commute with the critical seed. These are the two original-kernel hypotheses
needed by the whole-Z top-layer comparison.

In the large critical-image branch, the existing quadratic-plane theorem
constructs that plane and its lifts. The resulting original-source application
excludes critical relative index at least sixteen over F4, with the original
quotient, embedded cover, and adjacent-core actor retained. No later whole
outer-removal conclusion or central complement is used.

Source: Meierfrankenfeld--Stellmacher (1993), proof of (3.3), printed p.867.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterB.QuasisimpleSource
open Representation.SymplecticFourOrthogonalCover
variable {M J V : Type*} [Group M] [Group J] [AddCommGroup V] [Module (ZMod 2) V]
  {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}
  {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
  {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- Centralizing the original commutator lifts gives the inner and commuting
actor conclusions on the original whole Z-layer. -/
theorem critical_inner_plane_actors
    (path : CriticalPath R geometry a z)
    (Y : Subgroup (FreeAmalgam R)) (hYZ : Y ≤ stabilizer R z)
    (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (hcard : 2 < Nat.card F) (hcent : centralizer (B : Set J) = ⊥)
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R)
    (hj : Function.Injective j) (hjr : j.range = U R z)
    (κ : stabilizer R z →* J)
    (hk : κ.ker.map (stabilizer R z).subtype = C R z)
    (hB : ((Ltilde R z).subgroupOf (stabilizer R z)).map κ = B)
    (hconj : ∀ (g : stabilizer R z) (v : s.space.toSubmodule),
      j (Multiplicative.ofAdd (s.space.toRepresentation (κ g) v)) =
        (g : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(g : FreeAmalgam R)⁻¹)
    (π : U R z →* Multiplicative (Vector F))
    (hπ : ∀ w : s.space.toSubmodule,
      π ⟨j (Multiplicative.ofAdd w),by rw [←hjr]; exact ⟨_,rfl⟩⟩ =
        Multiplicative.ofAdd (MovedSection.coverProjection s e w))
    (P : Submodule F (Vector F)) (hP : (form F).orthogonal P=P)
    (hcover : ∀ v ∈ P, ∃ d : ((⁅Z R a,Z R z⁆ ⊓ U R z) : Subgroup (FreeAmalgam R)),
      (π ⟨d.val,d.property.2⟩).toAdd = v)
    (hfix : ∀ x : Z R a, ∀ v ∈ P,
      MovedSection.ambientAction s e
        (κ ⟨x,Z_le_stabilizer_of_dist_le a
          (geometry.exists_critical a path.start_color) path.critical.1.le x.property⟩) v=v)
    (hc : Y ≤ centralizer ((⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set _)) :
    Y ≤ Ltilde R z ⊔ centralizer (Z R z : Set (FreeAmalgam R)) ∧
      ⁅Z R a,Y⁆ ≤ centralizer (Z R z : Set (FreeAmalgam R)) := by
  let d : L (K := F) ≃* Sp F :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hcard)).trans
      Subgroup.topEquiv
  have hAZ : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hlifts : ∀ v ∈ P, ∃ w : s.space.toSubmodule,
      j (Multiplicative.ofAdd w) ∈ ⁅Z R a,Z R z⁆ ∧
        MovedSection.coverProjection s e w=v := by
    intro v hv
    obtain ⟨c,hc⟩ := hcover v hv
    have hcu : c.val ∈ j.range := by rw [hjr]; exact c.property.2
    obtain ⟨w,hw⟩ := hcu
    refine ⟨w.toAdd,hw ▸ c.property.1,?_⟩
    have he : (⟨j (Multiplicative.ofAdd w.toAdd),by rw [←hjr]; exact ⟨_,rfl⟩⟩ : U R z) =
        ⟨c.val,c.property.2⟩ := Subtype.ext hw
    have hh := congrArg Multiplicative.toAdd (hπ w.toAdd)
    rw [he,hc,toAdd_ofAdd] at hh
    exact hh.symm
  obtain ⟨hi,hc'⟩ := SymplecticNaturalNormalizer.centralizer_plane_lifts_inner_and_commutes
    (stabilizer R z) (Ltilde R z) (C R z) (Z R a) Y ⁅Z R a,Z R z⁆ hAZ hYZ
    κ B hB hk (hcent ▸ bot_le) hcard (e.groupEquiv.trans d)
    (MovedSection.ambientAction s e) (fun b w => MovedSection.ambientAction_component s e b w)
    s.space.toRepresentation j hj hconj (MovedSection.coverProjection s e).toLinearMap
    (fun g w => MovedSection.coverProjection_ambient s e g w) P hP hlifts hfix hc
  exact ⟨hi.trans (sup_le_sup_left (show C R z ≤ centralizer (Z R z : Set _) from inf_le_right) _),
    hc'.trans inf_le_right⟩



/-- The genuine large-actor plane supplies both inner-actor hypotheses of the
source comparison, with the original quotient kernel and marking retained. -/
theorem critical_large_actor_excluded_of_ambient_cover
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
    (hbad : ¬ ⁅Z R z,Y⁆ ≤ ⁅X R a,X R z⁆ ⊔ ⁅X R a ⊓ Q R z,Y⁆)
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
  exact CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_large_actor_excluded_of_card_four
    path hb Y σ p hp j hj hjr β hβact hker hinner hcomm hc hbad hF hlarge

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison

namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
open Theory.GroupTheory
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

/-- The source's actual critical quotient has index below sixteen in the bad
comparison branch. The original initial cover and the critical model actor
are constructed here; the inner-plane centralizer identities are proved from the actual plane. -/
theorem original_large_critical_index_lt_sixteen_of_local_actor
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
    (hbad : ¬ ⁅Z R z,Y⁆ ≤ ⁅X R a,X R z⁆ ⊔ ⁅X R a ⊓ Q R z,Y⁆) :
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
  exact critical_large_actor_excluded_of_ambient_cover path hb Y hYZ hFcard s e he hC
    j hj hjr κ hκC hκL hconj β hβmark hker hcentral hbad (by omega)



/-- The literal adjacent-core actor supplies the local containment needed by
the original large-index exclusion. -/
theorem original_large_critical_index_lt_sixteen_of_adjacent_core
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
    {t : Vertex R} (ht : Adjacent R z t) (hYQ : Y ≤ Q R t)
    (hcentral : Y ≤ centralizer ((⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set _))
    (hbad : ¬ ⁅Z R z,Y⁆ ≤ ⁅X R a,X R z⁆ ⊔ ⁅X R a ⊓ Q R z,Y⁆) :
    (Q R z).relIndex (Z R a) < 16 := by
  exact original_large_critical_index_lt_sixteen_of_local_actor R hms hp hne hQR hself
    hfaith q hq hcore hc hC hsq path hb Y
    (fun y hy => (hYQ hy).2 z (adjacent_symm R ht)) hcentral hbad

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
