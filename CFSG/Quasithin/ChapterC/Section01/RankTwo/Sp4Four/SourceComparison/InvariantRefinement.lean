module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.PlaneDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.LocalGroups
public import Theory.Representation.SymplecticFourOrthogonalCover.InvariantRefinement

/-!
# The source critical actor preserves a quadratic refinement

The bad displacement in MS93 (3.3) forces the full kernel of the moving
cover U_e to escape the critical commutator. The universal-cover theorem
then constructs a quadratic refinement invariant under the literal image
of Z_a. A marked plane-radical image consequently has order at most 2q.

The source displacement bound and critical plane image remain earlier-source
inputs. A separate sufficient plane calculation uses a Y-fixed supplement;
no decomposition of X_e is assumed in the general source consumer.
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
  {geometry : Geometry R} {a e t : Vertex R}

/-- The source edge radical normalizes the literal moving endpoint layer. -/
theorem endpoint_moving_normalized_by_edge
    (het : Adjacent R e t) (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ Q R t) :
    Y ≤ normalizer (U R e : Set (FreeAmalgam R)) := by
  intro y hy
  exact U_normalized e ((hY hy).2 e (adjacent_symm R het))

/-- The source bad displacement produces the quadratic refinement from the
literal moving cover, rather than assuming that the critical actor preserves one. -/
theorem critical_refinement_of_bad_displacement_bound
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    (Y : Subgroup (FreeAmalgam R))
    [Finite (U R e)] [IsElementaryAbelian 2 (U R e)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (σ : Representation (ZMod 2) (L (K := F)) (Additive (U R e)))
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (β : Z R a →* L (K := F))
    (hβ : ∀ z : Z R a, ∀ u : U R e,
      ((σ (β z) (Additive.ofMul u)).toMul : FreeAmalgam R) =
        (z:FreeAmalgam R)*u*(z:FreeAmalgam R)⁻¹)
    (hbound : ⁅Z R e,Y⁆ ≤ ⁅Z R a,Z R e⁆ ⊔
      p.toLinearMap.ker.toAddSubgroup.toSubgroup'.map (U R e).subtype)
    (hbad : ¬ ⁅Z R e,Y⁆ ≤ ⁅X R a,X R e⁆ ⊔ ⁅X R a ⊓ Q R e,Y⁆) :
    ∃ c : Vector F, ∀ z : Z R a, ∀ v,
      refinement c (binaryNatural (β z) v)=refinement c v := by
  apply ambient_cover_preserves_refinement_of_kernel_escape (U R e) (⁅Z R a,Z R e⁆)
    (Z R a) σ p hp β hβ (commutator_mono le_rfl (U_le_Z e))
  intro hker
  apply hbad
  exact (hbound.trans (sup_le le_rfl hker)).trans
    ((critical_commutator_le_auxiliary path hb).trans le_sup_left)

/-- The numerical source comparison for a literally marked plane-radical
image. The quadratic-preservation premise has been discharged from the
original bad displacement and the moving-cover bound. -/
theorem critical_plane_actor_card_le_of_bad_displacement_bound
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    (Y : Subgroup (FreeAmalgam R))
    [Finite (U R e)] [IsElementaryAbelian 2 (U R e)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (σ : Representation (ZMod 2) (L (K := F)) (Additive (U R e)))
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (β : Z R a →* L (K := F))
    (hβ : ∀ z : Z R a, ∀ u : U R e,
      ((σ (β z) (Additive.ofMul u)).toMul : FreeAmalgam R) =
        (z:FreeAmalgam R)*u*(z:FreeAmalgam R)⁻¹)
    (hbound : ⁅Z R e,Y⁆ ≤ ⁅Z R a,Z R e⁆ ⊔
      p.toLinearMap.ker.toAddSubgroup.toSubgroup'.map (U R e).subtype)
    (hbad : ¬ ⁅Z R e,Y⁆ ≤ ⁅X R a,X R e⁆ ⊔ ⁅X R a ⊓ Q R e,Y⁆)
    (δ : Z R a →* Plane.radical (F := F))
    (hδ : ∀ z, (δ z).val.val = (β z).val) :
    Nat.card δ.range ≤ 2*Nat.card F := by
  obtain ⟨c,hc⟩ := critical_refinement_of_bad_displacement_bound path hb Y σ p hp β hβ hbound hbad
  apply card_radical_subgroup_le δ.range c
  intro g v
  obtain ⟨z,hz⟩ := g.property
  rw [←hz,hδ]
  exact hc z v

/-- Over the four-element field the original plane actor cannot have the
large order occurring in the first branch of MS93 (3.3). -/
theorem critical_plane_actor_not_large_of_card_four
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    (Y : Subgroup (FreeAmalgam R))
    [Finite (U R e)] [IsElementaryAbelian 2 (U R e)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (σ : Representation (ZMod 2) (L (K := F)) (Additive (U R e)))
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (β : Z R a →* L (K := F))
    (hβ : ∀ z : Z R a, ∀ u : U R e,
      ((σ (β z) (Additive.ofMul u)).toMul : FreeAmalgam R) =
        (z:FreeAmalgam R)*u*(z:FreeAmalgam R)⁻¹)
    (hbound : ⁅Z R e,Y⁆ ≤ ⁅Z R a,Z R e⁆ ⊔
      p.toLinearMap.ker.toAddSubgroup.toSubgroup'.map (U R e).subtype)
    (hbad : ¬ ⁅Z R e,Y⁆ ≤ ⁅X R a,X R e⁆ ⊔ ⁅X R a ⊓ Q R e,Y⁆)
    (δ : Z R a →* Plane.radical (F := F))
    (hδ : ∀ z, (δ z).val.val = (β z).val)
    (hF : Nat.card F=4) (hlarge : 16 ≤ Nat.card δ.range) : False := by
  have hcard := critical_plane_actor_card_le_of_bad_displacement_bound
    path hb Y σ p hp β hβ hbound hbad δ hδ
  omega

/-- The actual source bad displacement forces a quadratic refinement preserved
by the original critical actor. The cover belongs to U_e, retaining its full
central kernel; the critical plane and Y-fixed supplement are separate inputs. -/
theorem critical_refinement_of_bad_displacement_of_fixed_supplement
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    (het : Adjacent R e t)
    (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ Q R t)
    (hc : Y ≤ centralizer ((⁅Z R a,Z R e⁆ : Subgroup (FreeAmalgam R)) : Set _))
    [Finite (U R e)] [IsElementaryAbelian 2 (U R e)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (σ : Representation (ZMod 2) (L (K := F)) (Additive (U R e)))
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (β : Z R a →* L (K := F))
    (hβ : ∀ z : Z R a, ∀ u : U R e,
      ((σ (β z) (Additive.ofMul u)).toMul : FreeAmalgam R) =
        (z:FreeAmalgam R)*u*(z:FreeAmalgam R)⁻¹)
    (π : U R e →* Multiplicative (Vector F))
    (hπ : ∀ u : U R e, π u = Multiplicative.ofAdd (p (Additive.ofMul u)))
    (α : Y →* Sp F)
    (hact : ∀ (y : Y) (u : U R e),
      π ⟨y.val*u.val*y.val⁻¹,
        (mem_normalizer_iff.mp (endpoint_moving_normalized_by_edge het Y hY y.property)
          u.val).mp u.property⟩ = Multiplicative.ofAdd (α y • (π u).toAdd))
    (W : Submodule F (Vector F)) (hW : (form F).orthogonal W = W)
    (hcover : ∀ w ∈ W, ∃ d : ((⁅Z R a,Z R e⁆ ⊓ U R e) : Subgroup (FreeAmalgam R)),
      (π ⟨d.val,d.property.2⟩).toAdd = w)
    (hfixedSupplement : ∀ z ∈ Z R e, ∃ u ∈ U R e,
      ∃ c ∈ centralizer (Y : Set (FreeAmalgam R)), z = u*c)
    (hbad : ¬ ⁅Z R e,Y⁆ ≤ ⁅X R a,X R e⁆ ⊔ ⁅X R a ⊓ Q R e,Y⁆) :
    ∃ c : Vector F, ∀ z : Z R a, ∀ v,
      refinement c (binaryNatural (β z) v)=refinement c v := by
  have hmove : ⁅Z R e,Y⁆ ≤ ⁅U R e,Y⁆ := by
    apply commutator_le.mpr
    intro z hz y hy
    obtain ⟨u,hu,c,hc,hz⟩ := hfixedSupplement z hz
    rw [hz,commutatorElement_mul_left_eq_conj_mul,
      show ⁅c,y⁆=1 from commutatorElement_eq_one_iff_mul_comm.mpr (hc y hy).symm]
    simpa only [mul_one,mul_inv_cancel,one_mul] using commutator_mem_commutator hu hy
  have hbound : ⁅Z R e,Y⁆ ≤ ⁅Z R a,Z R e⁆ ⊔ π.ker.map (U R e).subtype := by
    apply hmove.trans
    exact (commutator_le_plane_sup_kernel (U R e) Y (⁅Z R a,Z R e⁆ ⊓ U R e)
      inf_le_right (endpoint_moving_normalized_by_edge het Y hY) π α hact W hW hcover
      (hc.trans (centralizer_le inf_le_left))).trans (sup_le_sup inf_le_left le_rfl)
  have hk : ¬ π.ker.map (U R e).subtype ≤ ⁅Z R a,Z R e⁆ := by
    intro hker
    apply hbad
    exact (hbound.trans (sup_le le_rfl hker)).trans
      ((critical_commutator_le_auxiliary path hb).trans le_sup_left)
  have hker : p.toLinearMap.ker.toAddSubgroup.toSubgroup' = π.ker := by
    ext u
    change p (Additive.ofMul u)=0 ↔ π u=1
    rw [hπ]
    exact ofAdd_eq_one.symm
  apply ambient_cover_preserves_refinement_of_kernel_escape (U R e) (⁅Z R a,Z R e⁆)
    (Z R a) σ p hp β hβ (commutator_mono le_rfl (U_le_Z e))
  rwa [hker]

/-- Direct application to the initial producer's embedded moved-space cover.
Its kernel-centralizer equivalence and residual conjugation map are retained. -/
theorem critical_refinement_of_embedded_cover
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    (Y : Subgroup (FreeAmalgam R))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* FreeAmalgam R) (hjr : j.range = U R e)
    (f : Ltilde R e →* L (K := F))
    (hact : ∀ k : Ltilde R e, ∀ w : W,
      j (Multiplicative.ofAdd (σ (f k) w)) =
        (k:FreeAmalgam R)*j (Multiplicative.ofAdd w)*(k:FreeAmalgam R)⁻¹)
    (hker : ∀ w : W, p w = 0 ↔
      j (Multiplicative.ofAdd w) ∈ centralizer (Ltilde R e : Set (FreeAmalgam R)))
    (hinner : Z R a ≤ Ltilde R e)
    (hbound : ⁅Z R e,Y⁆ ≤ ⁅Z R a,Z R e⁆ ⊔
      (U R e ⊓ centralizer (Ltilde R e : Set (FreeAmalgam R))))
    (hbad : ¬ ⁅Z R e,Y⁆ ≤ ⁅X R a,X R e⁆ ⊔ ⁅X R a ⊓ Q R e,Y⁆) :
    ∃ c : Vector F, ∀ z : Z R a, ∀ v,
      refinement c (binaryNatural (f ⟨z.val,hinner z.property⟩) v)=refinement c v := by
  have hk : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
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
  apply embedded_cover_preserves_refinement_of_kernel_escape
    (⁅Z R a,Z R e⁆) (Z R a) σ p hp j
    (f.comp (inclusion hinner)) (fun z w => hact ⟨z.val,hinner z.property⟩ w)
  · rw [hjr]
    exact commutator_mono le_rfl (U_le_Z e)
  · intro hle
    apply hbad
    rw [hk] at hle
    exact (hbound.trans (sup_le le_rfl hle)).trans
      ((critical_commutator_le_auxiliary path hb).trans le_sup_left)

/-- The initial embedded cover accepts an actual critical actor map even when
the actor is inner only modulo the centralizer of the original Z-layer. -/
theorem critical_refinement_of_embedded_actor
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    (Y : Subgroup (FreeAmalgam R))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* FreeAmalgam R) (hjr : j.range = U R e)
    (β : Z R a →* L (K := F))
    (hact : ∀ k : Z R a, ∀ w : W,
      j (Multiplicative.ofAdd (σ (β k) w)) =
        (k:FreeAmalgam R)*j (Multiplicative.ofAdd w)*(k:FreeAmalgam R)⁻¹)
    (hker : ∀ w : W, p w = 0 ↔
      j (Multiplicative.ofAdd w) ∈ centralizer (Ltilde R e : Set (FreeAmalgam R)))
    (hbound : ⁅Z R e,Y⁆ ≤ ⁅Z R a,Z R e⁆ ⊔
      (U R e ⊓ centralizer (Ltilde R e : Set (FreeAmalgam R))))
    (hbad : ¬ ⁅Z R e,Y⁆ ≤ ⁅X R a,X R e⁆ ⊔ ⁅X R a ⊓ Q R e,Y⁆) :
    ∃ c : Vector F, ∀ z : Z R a, ∀ v,
      refinement c (binaryNatural (β z) v)=refinement c v := by
  have hk : p.toLinearMap.ker.toAddSubgroup.toSubgroup.map j =
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
  apply embedded_cover_preserves_refinement_of_kernel_escape
    (⁅Z R a,Z R e⁆) (Z R a) σ p hp j
    β hact
  · rw [hjr]
    exact commutator_mono le_rfl (U_le_Z e)
  · intro hle
    apply hbad
    rw [hk] at hle
    exact (hbound.trans (sup_le le_rfl hle)).trans
      ((critical_commutator_le_auxiliary path hb).trans le_sup_left)


end CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
