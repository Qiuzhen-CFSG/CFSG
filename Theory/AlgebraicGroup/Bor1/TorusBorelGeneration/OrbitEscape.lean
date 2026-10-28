module

public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.BorelOrbit
public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.ProjectiveHyperplane

/-!
# Torus fixed-point escape on complete Borel orbits

The orbit of a Borel-fixed point is closed by the complete homogeneous orbit
lemma. Its actual reduced closed carrier is complete and connected. An
equivariant nonconstant projective image then admits a separating torus fixed
point by the invariant-hyperplane argument. Applying this to the diagonal
orbit in G/B times the Chevalley projective model simultaneously constructs
the fixed lift and its escape from the parabolic base coset in Borel 13.7.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped LinearAlgebra.Projectivization
namespace Theory.AlgebraicGroup.Variety.Geometric.MorphicAction
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
variable {E : Type u} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
variable {X : Geometric k}

theorem point_mem_orbit_range_iff (A : MorphicAction G X) (x y : Point X) :
    y.1 (IsLocalRing.closedPoint k) ∈ Set.range (A.orbitMorphismAt x).hom ↔
      ∃ g : Variety.Point G, A.toMulAction.smul g x = y := by
  rw [← (A.orbitMorphismAt x).point_mem_range_iff_closedPoint_mem_range y]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨affinePointEquiv G g, ?_⟩
    simpa only [Equiv.symm_apply_apply, hg] using
      (A.orbitMorphismAt_apply x (affinePointEquiv G g)).symm
  · rintro ⟨g, rfl⟩
    exact ⟨(affinePointEquiv G).symm g, A.orbitMorphismAt_apply x g⟩

/-- The actual projective orbit with a Borel stabilizing its base point has
another torus fixed point whenever it is not a singleton. -/
theorem exists_torus_fixedPoint_on_complete_borel_orbit
    (A : MorphicAction G X) (hX : IsComplete X) (hG : Variety.IsConnected G)
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (T : ClosedSubgroup G) (hT : IsTorus T.carrierVariety)
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (f : Morphism X (projectiveSpace k E))
    (he : ∀ (g : Variety.Point G) (p : Point X),
      projectiveSpacePointEquivOf b (f (A.toMulAction.smul g p)) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b (f p)))
    (x : Point X)
    (hfix : ∀ g ∈ B.toSubgroup, A.toMulAction.smul g x = x)
    (z : Variety.Point G) (hz : f (A.toMulAction.smul z x) ≠ f x) :
    ∃ g : Variety.Point G,
      (∀ t : Variety.Point T.carrierVariety,
        A.toMulAction.smul (T.includePoint t) (A.toMulAction.smul g x) =
          A.toMulAction.smul g x) ∧ f (A.toMulAction.smul g x) ≠ f x := by
  let P := X
  let Z : Closeds P.toScheme :=
    ⟨Set.range (A.orbitMorphismAt x).hom, A.orbit_isClosed_of_borel_fixed hG B hB x hfix⟩
  let C := reducedClosedSubvariety P Z
  have hinv : ∀ (g : Variety.Point G) (p : Point P),
      p.1 (IsLocalRing.closedPoint k) ∈ Z →
      (A.toMulAction.smul g p).1 (IsLocalRing.closedPoint k) ∈ Z := by
    intro g p hp
    obtain ⟨h, rfl⟩ := (A.point_mem_orbit_range_iff x p).mp hp
    apply (A.point_mem_orbit_range_iff x _).mpr
    exact ⟨g * h, A.toMulAction.mul_smul g h x⟩
  let R := A.onInvariantReducedClosedSubvariety Z hinv
  let q := restrictToReducedClosedSubvariety Z (A.orbitMorphismAt x) (Set.Subset.refl _)
  have hq : q.hom ≫ C.inclusion.hom = (A.orbitMorphismAt x).hom :=
    congrArg Morphism.hom (restrictToReducedClosedSubvariety_inclusion Z
      (A.orbitMorphismAt x) (Set.Subset.refl _))
  have hsurj : Function.Surjective q.hom := by
    intro y
    have hy : C.inclusion.hom y ∈ Set.range (A.orbitMorphismAt x).hom := by
      change C.inclusion.hom y ∈ (Z : Set P.toScheme)
      rw [← reducedClosedSubvariety_range P Z]
      exact ⟨y, rfl⟩
    obtain ⟨g, hg⟩ := hy
    refine ⟨g, C.inclusion.hom.isEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hq]
    exact hg
  have hCconn : IsConnected C.toGeometric := by
    letI : IrreducibleSpace (ofAffine G).toScheme :=
      ofAffine_isIrreducible_of_isConnected G hG
    letI : IrreducibleSpace C.toGeometric.toScheme := hsurj.irreducibleSpace q.hom.continuous
    exact (inferInstance : ConnectedSpace C.toGeometric.toScheme)
  have hxZ : x.1 (IsLocalRing.closedPoint k) ∈ Z :=
    (A.point_mem_orbit_range_iff x x).mpr ⟨1, A.toMulAction.one_smul x⟩
  have hzZ : (A.toMulAction.smul z x).1 (IsLocalRing.closedPoint k) ∈ Z :=
    (A.point_mem_orbit_range_iff x _).mpr ⟨z, rfl⟩
  obtain ⟨x', hx', _⟩ := (point_mem_reducedClosedSubvariety_iff P Z x).mp hxZ
  obtain ⟨z', hz', _⟩ := (point_mem_reducedClosedSubvariety_iff P Z _).mp hzZ
  have hcomp : ∀ (t : Variety.Point T.carrierVariety) (p : Point C.toGeometric),
      projectiveSpacePointEquivOf b
          (f (C.inclusion (R.toMulAction.smul (T.includePoint t) p))) =
      Projectivization.map (ρ.action (T.includePoint t)).1
        (ρ.action (T.includePoint t)).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b (f (C.inclusion p))) := by
    intro t p
    rw [A.onInvariantReducedClosedSubvariety_inclusion]
    exact he _ _
  obtain ⟨y, hy, hxy⟩ := R.exists_torus_fixedPoint_separating
    (reducedClosedSubvariety_isComplete Z hX) hCconn
    ρ hρ T hT b (C.inclusion.comp f) hcomp x' z' (by change f (C.inclusion x') ≠ f (C.inclusion z'); rw [hx', hz']; exact hz.symm)
  have hyZ : (C.inclusion y).1 (IsLocalRing.closedPoint k) ∈ Z := by
    change C.inclusion.hom (y.1 (IsLocalRing.closedPoint k)) ∈ (Z : Set P.toScheme)
    rw [← reducedClosedSubvariety_range P Z]
    exact ⟨y.1 (IsLocalRing.closedPoint k), rfl⟩
  obtain ⟨g, hg⟩ := (A.point_mem_orbit_range_iff x (C.inclusion y)).mp hyZ
  refine ⟨g, ?_, ?_⟩
  · intro t
    rw [hg]
    have hh := A.onInvariantReducedClosedSubvariety_inclusion Z hinv (T.includePoint t) y
    rw [hy] at hh
    exact hh.symm
  · rw [hg, ← hx']
    exact hxy

end Theory.AlgebraicGroup.Variety.Geometric.MorphicAction
