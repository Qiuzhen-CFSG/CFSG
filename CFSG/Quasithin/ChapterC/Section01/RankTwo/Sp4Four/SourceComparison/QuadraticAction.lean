module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.PlaneDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.LocalGroups
public import Theory.Representation.SymplecticFourOrthogonalCover.Universal
public import Theory.ElementaryAbelian.VectorSpace

/-!
# Quadratic action at the actual critical pair

The critical endpoints normalize one another's seeds, so their commutator
lies in both seeds. At positive critical distance those seeds are elementary
abelian. Hence the original Z_a actor fixes every displacement of U_e.
The literal quotient projection transports this to the natural module.

This supplies the quadratic-action input for the plane-image and inner-actor
comparisons in MS93 (3.2)--(3.3), printed pp.863--867. No binary natural-module
recognition or decomposition of X_e is used.
-/

public section
open Subgroup Representation Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
variable {M : Type*} [Group M] {R : Subgroup M}
  {geometry : Geometry R} {a e : Vertex R}

/-- The critical commutator lies in the starting seed as well as the endpoint seed. -/
theorem critical_commutator_le_start_seed (path : CriticalPath R geometry a e) :
    ⁅Z R a,Z R e⁆ ≤ Z R a := by
  rw [commutator_comm]
  apply le_normalizer_iff_commutator_le_right.mp
  apply (Z_le_stabilizer_of_dist_le e (geometry.exists_critical e path.end_color) ?_).trans
    (Z_normalized R a)
  rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
    geometry.distance_constant e path.end_color]

/-- Conjugation by the original starting seed is quadratic on the moving endpoint layer. -/
theorem critical_actor_quadratic
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    [IsElementaryAbelian 2 (U R e)]
    {D : Type*} [Group D]
    (σ : Representation (ZMod 2) D (Additive (U R e)))
    (β : Z R a →* D)
    (hβ : ∀ z : Z R a, ∀ u : U R e,
      ((σ (β z) (Additive.ofMul u)).toMul : FreeAmalgam R) =
        (z:FreeAmalgam R)*u*(z:FreeAmalgam R)⁻¹) :
    BinaryOffender.IsQuadratic σ β.range := by
  let : IsElementaryAbelian 2 (Z R a) := geometry.Z_elementary hb a path.start_color
  intro x hx y hy w
  obtain ⟨x,rfl⟩ := hx
  obtain ⟨y,rfl⟩ := hy
  let d := σ (β y) w-w
  have hd : (d.toMul:FreeAmalgam R) ∈ Z R a := by
    change ((σ (β y) w-w).toMul:FreeAmalgam R) ∈ Z R a
    rw [toMul_sub,div_eq_mul_inv]
    change ((σ (β y) w).toMul:FreeAmalgam R) * (w.toMul:FreeAmalgam R)⁻¹ ∈ Z R a
    have hh := hβ y w.toMul
    simp only [ofMul_toMul] at hh
    rw [hh]
    exact critical_commutator_le_start_seed path
      (commutator_mem_commutator y.property (U_le_Z e w.toMul.property))
  change σ (β x) d=d
  apply Additive.toMul.injective
  apply Subtype.ext
  have hh := hβ x d.toMul
  simp only [ofMul_toMul] at hh
  rw [hh]
  have hc := (Z R a).le_centralizer hd x.val x.property
  rw [hc,mul_inv_cancel_right]

open Representation.SymplecticFourOrthogonalCover

/-- The actual natural quotient inherits the quadratic critical actor, with
no separate quadratic-action hypothesis. -/
theorem critical_natural_actor_quadratic
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    [IsElementaryAbelian 2 (U R e)]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (σ : Representation (ZMod 2) (L (K := F)) (Additive (U R e)))
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (β : Z R a →* L (K := F))
    (hβ : ∀ z : Z R a, ∀ u : U R e,
      ((σ (β z) (Additive.ofMul u)).toMul : FreeAmalgam R) =
        (z:FreeAmalgam R)*u*(z:FreeAmalgam R)⁻¹) :
    BinaryOffender.IsQuadratic (binaryNatural (K := F)) β.range := by
  intro x hx y hy v
  obtain ⟨w,rfl⟩ := hp.1 v
  have h := congrArg p (critical_actor_quadratic path hb σ β hβ x hx y hy w)
  simpa only [map_sub,p.isIntertwining] using h

/-- Quadraticity on the initial producer's canonical embedded moved space. -/
theorem critical_embedded_actor_quadratic
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {D : Type*} [Group D]
    (σ : Representation (ZMod 2) D W)
    (j : Multiplicative W →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R e) (β : Z R a →* D)
    (hβ : ∀ z : Z R a, ∀ w : W,
      j (Multiplicative.ofAdd (σ (β z) w)) =
        (z:FreeAmalgam R)*j (Multiplicative.ofAdd w)*(z:FreeAmalgam R)⁻¹) :
    BinaryOffender.IsQuadratic σ β.range := by
  let : IsElementaryAbelian 2 (Z R a) := geometry.Z_elementary hb a path.start_color
  intro x hx y hy w
  obtain ⟨x,rfl⟩ := hx
  obtain ⟨y,rfl⟩ := hy
  let d := σ (β y) w-w
  have hd : j (Multiplicative.ofAdd d) ∈ Z R a := by
    change j (Multiplicative.ofAdd (σ (β y) w-w)) ∈ Z R a
    rw [ofAdd_sub,map_div,div_eq_mul_inv,hβ]
    apply critical_commutator_le_start_seed path
    apply commutator_mem_commutator y.property
    apply U_le_Z e
    rw [←hjr]
    exact ⟨Multiplicative.ofAdd w,rfl⟩
  change σ (β x) d=d
  apply Multiplicative.ofAdd.injective
  apply hj
  rw [hβ]
  have hc := (Z R a).le_centralizer hd x.val x.property
  rw [hc,mul_inv_cancel_right]

open Representation.SymplecticFourOrthogonalCover

/-- The embedded initial cover transmits the actual quadratic critical action
to its natural quotient. -/
theorem critical_embedded_natural_actor_quadratic
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (σ : Representation (ZMod 2) (L (K := F)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R e) (β : Z R a →* L (K := F))
    (hβ : ∀ z : Z R a, ∀ w : W,
      j (Multiplicative.ofAdd (σ (β z) w)) =
        (z:FreeAmalgam R)*j (Multiplicative.ofAdd w)*(z:FreeAmalgam R)⁻¹) :
    BinaryOffender.IsQuadratic (binaryNatural (K := F)) β.range := by
  intro x hx y hy v
  obtain ⟨w,rfl⟩ := hp.1 v
  have h := congrArg p (critical_embedded_actor_quadratic path hb σ j hj hjr β hβ x hx y hy w)
  simpa only [map_sub,p.isIntertwining] using h

end CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
