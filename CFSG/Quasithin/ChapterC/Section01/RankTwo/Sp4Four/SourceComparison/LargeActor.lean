module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.PlaneCover
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.InvariantRefinement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.TopLayerBound
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.ArbitraryOrthogonalActors
public import Theory.Representation.SymplecticFourOrthogonalCover.EmbeddedProjection
/-!
# The source large critical actor bound

The initial embedded moving cover determines a literal projection on U_e.
Quadratic critical action constructs its self-orthogonal fixed plane and
lifts that plane into the original critical commutator. Inner action modulo
the centralizer of Z_e, together with commuting natural actors, gives the
whole-Z displacement bound by the three-subgroup argument. Source bad
displacement forces the cover kernel to escape, hence gives an invariant
quadratic refinement. The arbitrary-plane orthogonal count bounds the
critical natural image by 2q, excluding order at least sixteen over F4.

Only the earlier inner-actor and original-kernel commutator facts remain
explicit. No plane marking, fixed supplement of Z_e, refinement-preservation
hypothesis, or splitting of a central cover attachment is assumed.
Source: MS93 (3.3), first symplectic paragraph, printed p.867.
-/

public section
open Subgroup Representation Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
variable {M : Type*} [Group M] {R : Subgroup M}
  {geometry : Geometry R} {a e : Vertex R}

/-- The actual source bad displacement bounds a large critical natural actor
by 2q, deriving its plane and quadratic refinement from the embedded cover. -/
theorem critical_large_actor_card_le
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
    (hbad : ¬ ⁅Z R e,Y⁆ ≤ ⁅X R a,X R e⁆ ⊔ ⁅X R a ⊓ Q R e,Y⁆)
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
  obtain ⟨c,hc'⟩ := critical_refinement_of_embedded_actor path hb Y σ p hp j hjr β hβ
    hker hbound hbad
  rw [←hcard]
  apply card_le_of_fixes_self_orthogonal_plane α.range (displacementSpace α.range) hP ?_ c ?_
  · rintro ⟨g,hg⟩ v hv
    have hf : v ∈ TwoLocalCover.fixedSpace α.range := by
      rw [←orthogonal_displacementSpace,hP]
      exact hv
    exact hf g hg
  · rintro ⟨g,⟨z,rfl⟩⟩ v
    exact hc' z v
/-- The first large-actor branch of the source comparison is impossible over F4. -/
theorem critical_large_actor_excluded_of_card_four
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
    (hbad : ¬ ⁅Z R e,Y⁆ ≤ ⁅X R a,X R e⁆ ⊔ ⁅X R a ⊓ Q R e,Y⁆)
    (hF : Nat.card F=4) (hlarge : 16 ≤ Nat.card β.range) : False := by
  have hgt : Nat.card F < Nat.card β.range := by omega
  have hc := critical_large_actor_card_le path hb Y σ p hp j hj hjr β hβ hker
    hinner hcomm hc hbad hgt
  omega

end CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
