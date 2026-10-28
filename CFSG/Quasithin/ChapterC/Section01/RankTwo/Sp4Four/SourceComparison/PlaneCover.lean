module
public import Theory.SpecificGroups.SymplecticFour.QuadraticPlane
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.QuadraticAction
/-!
# The actual critical commutator covers the natural fixed plane

The native critical-pair argument makes the starting seed quadratic on the
embedded moving cover. The literal quotient inherits this action. If its
natural image has order greater than q, its field-linear displacement is a
self-orthogonal plane and is exactly its fixed space. Surjectivity and scalar
restriction of coinvariants lift every vector of this plane into the actual
critical commutator, with the producer's original projection retained.

These are the fixed-space and plane-cover inputs to TopLayerBound in the
first symplectic branch of MS93 (3.3), printed p.867.
-/

public section
open Subgroup Representation Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
variable {M : Type*} [Group M] {R : Subgroup M}
  {geometry : Geometry R} {a e : Vertex R}

/-- The literal critical image determines its own plane and the original
critical commutator covers every vector in it. -/
theorem critical_displacement_plane_and_cover
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {D : Type*} [Group D]
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (σ : Representation (ZMod 2) D W)
    (j : Multiplicative W →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R e) (β : Z R a →* D)
    (hβ : ∀ z : Z R a, ∀ w : W,
      j (Multiplicative.ofAdd (σ (β z) w)) =
        (z:FreeAmalgam R)*j (Multiplicative.ofAdd w)*(z:FreeAmalgam R)⁻¹)
    (p : W →ₗ[ZMod 2] Vector F) (hp : Function.Surjective p)
    (α : Z R a →* Sp F)
    (hα : ∀ z : Z R a, ∀ w : W, p (σ (β z) w) = α z • p w)
    (π : U R e →* Multiplicative (Vector F))
    (hπ : ∀ w : W, π ⟨j (Multiplicative.ofAdd w),by rw [←hjr]; exact ⟨_,rfl⟩⟩ =
      Multiplicative.ofAdd (p w))
    (hlarge : Nat.card F < Nat.card α.range) :
    (form F).orthogonal (displacementSpace α.range) = displacementSpace α.range ∧
    (∀ v : Vector F, (∀ z : Z R a, α z • v=v) → v ∈ displacementSpace α.range) ∧
    (∀ v ∈ displacementSpace α.range,
      ∃ d : ((⁅Z R a,Z R e⁆ ⊓ U R e) : Subgroup (FreeAmalgam R)),
        (π ⟨d.val,d.property.2⟩).toAdd = v) := by
  have hq : ∀ x ∈ α.range, ∀ y ∈ α.range, ∀ v : Vector F,
      x • (y • v-v)=y • v-v := by
    rintro x ⟨z,rfl⟩ y ⟨t,rfl⟩ v
    obtain ⟨w,rfl⟩ := hp v
    have h := congrArg p (critical_embedded_actor_quadratic path hb σ j hj hjr β hβ
      (β z) ⟨z,rfl⟩ (β t) ⟨t,rfl⟩ w)
    simpa only [hα,map_sub,smul_sub] using h
  have hself := large_quadratic_displacement_self_orthogonal α.range hq hlarge
  refine ⟨hself,?_,?_⟩
  · intro v hv
    rw [←hself,orthogonal_displacementSpace]
    rintro g ⟨z,rfl⟩
    exact hv z
  · intro v hv
    let τ : Representation (ZMod 2) (Z R a) (Vector F) :=
      restrictScalars ((symplecticNatural 2).comp α)
    let pA : Representation.IntertwiningMap (σ.comp β) τ :=
      p.intertwiningMap_of_isIntertwiningMap _ _ hα
    have hv' : v ∈ Coinvariants.ker τ := by
      rw [coinvariants_restrictScalars]
      rwa [displacementSpace_range_eq] at hv
    rw [←map_coinvariants_of_surjective pA hp] at hv'
    obtain ⟨w,hw,rfl⟩ := hv'
    let T : Submodule (ZMod 2) W := AddSubgroup.toZModSubmodule 2
      ((⁅Z R a,Z R e⁆).comap j).toAddSubgroup'
    have hT : Coinvariants.ker (σ.comp β) ≤ T := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨z,w⟩,rfl⟩
      change j (Multiplicative.ofAdd (σ (β z) w-w)) ∈ ⁅Z R a,Z R e⁆
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hβ]
      apply commutator_mem_commutator z.property
      apply U_le_Z e
      rw [←hjr]
      exact ⟨Multiplicative.ofAdd w,rfl⟩
    refine ⟨⟨j (Multiplicative.ofAdd w),hT hw,by rw [←hjr]; exact ⟨_,rfl⟩⟩,?_⟩
    change (π ⟨j (Multiplicative.ofAdd w),_⟩).toAdd = p w
    rw [hπ,toAdd_ofAdd]
end CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
