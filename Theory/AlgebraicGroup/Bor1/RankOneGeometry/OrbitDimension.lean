module

public import Theory.AlgebraicGroup.Bor1.RankOneGeometry.ThreeFixedPoints
public import Theory.AlgebraicGroup.Bor1.RankOneGeometry.FixedBorels
public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.OrbitEscape
public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.ChevalleyAction
/-!
# The actual projective Borel orbit has rank-one dimension

A Chevalley projective action has the prescribed Borel as its exact stabilizer.
Its orbit is complete and irreducible. If its dimension were at least two,
the actual torus action would have three distinct fixed points; those would
give three different Borels through the rank-one maximal torus, contradicting
the intrinsic two-Borel theorem. The final existence theorem instantiates the
actual Chevalley producer, leaving no projective-model assumption.

This is the dimensional part of Borel, *Linear Algebraic Groups*, §13.13(3).
The rationality and projective-line identification of the curve are separate.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open scoped LinearAlgebra.Projectivization
namespace Theory.AlgebraicGroup.Bor1.RankOneGeometry
open Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {E : Type u} [AddCommGroup E] [Module k E] [FiniteDimensional k E]

theorem projective_borel_orbit_dimension_le_one
    (hG : Variety.IsConnected G) (T : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdimT : Variety.dimension T.carrierVariety=1)
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B)
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (A : MorphicAction G (projectiveSpace k E)) (x : Point (projectiveSpace k E))
    (he : ∀ (g : Variety.Point G) (p : Point (projectiveSpace k E)),
      projectiveSpacePointEquivOf b (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b p))
    (hstab : ∀ g : Variety.Point G, A.toMulAction.smul g x = x ↔ g ∈ B.toSubgroup) :
    dimension (A.orbitSubvariety x).toGeometric ≤ 1 := by
  classical
  let P := projectiveSpace k E
  have hclosed := A.orbit_isClosed_of_borel_fixed hG B hB x (fun g hg => (hstab g).mpr hg)
  let Z : Closeds P.toScheme := ⟨Set.range (A.orbitMorphismAt x).hom,hclosed⟩
  let C := reducedClosedSubvariety P Z
  have hinv : ∀ (g : Variety.Point G) (p : Point P),
      p.1 (IsLocalRing.closedPoint k) ∈ Z →
      (A.toMulAction.smul g p).1 (IsLocalRing.closedPoint k) ∈ Z := by
    intro g p hp
    obtain ⟨a,rfl⟩ := (A.point_mem_orbit_range_iff x p).mp hp
    exact (A.point_mem_orbit_range_iff x _).mpr ⟨g*a,A.toMulAction.mul_smul g a x⟩
  let R := A.onInvariantReducedClosedSubvariety Z hinv
  have hCirr : IrreducibleSpace C.toGeometric.toScheme := by
    let e := C.inclusion.hom.isClosedEmbedding.isEmbedding.toHomeomorph
    let er : Set.range C.inclusion.hom ≃ₜ Set.range (A.orbitMorphismAt x).hom :=
      Homeomorph.setCongr (reducedClosedSubvariety_range P Z)
    letI : IrreducibleSpace (ofAffine G).toScheme := ofAffine_isIrreducible_of_isConnected G hG
    letI : IrreducibleSpace (Set.range (A.orbitMorphismAt x).hom) :=
      Subtype.irreducibleSpace (by
        rw [←Set.image_univ]
        exact (IrreducibleSpace.isIrreducible_univ _).image _
          (A.orbitMorphismAt x).hom.continuous.continuousOn)
    exact (e.trans er).irreducibleSpace_iff.mpr inferInstance
  letI := hCirr
  have horbit (y : Point C.toGeometric) :
      ∃ g : Variety.Point G,A.toMulAction.smul g x = C.inclusion y := by
    apply (A.point_mem_orbit_range_iff x _).mp
    change C.inclusion.hom (y.1 (IsLocalRing.closedPoint k)) ∈ (Z : Set P.toScheme)
    rw [←reducedClosedSubvariety_range P Z]
    exact ⟨_,rfl⟩
  have hCdim : dimension C.toGeometric ≤ 1 := by
    by_contra h
    have htwo : 2 ≤ dimension C.toGeometric :=
      (ENat.WithBot.add_one_le_iff (n := 1)).mpr (lt_of_not_ge h)
    have heR (t : Variety.Point T.carrierVariety) (p : Point C.toGeometric) :
        projectiveSpacePointEquivOf b (C.inclusion (R.toMulAction.smul (T.includePoint t) p)) =
        Projectivization.map (ρ.action (T.includePoint t)).1
          (ρ.action (T.includePoint t)).toLinearEquiv.injective
          (projectiveSpacePointEquivOf b (C.inclusion p)) := by
      rw [A.onInvariantReducedClosedSubvariety_inclusion]
      exact he _ _
    obtain ⟨u,v,w,huf,hvf,hwf,huv,huw,hvw⟩ :=
      R.exists_three_torus_fixedPoints_of_dimension_ge_two T hT.1
        (reducedClosedSubvariety_isComplete Z (projectiveSpace_isComplete k E))
        htwo ρ hρ b C.inclusion heR
    obtain ⟨g,hg⟩ := horbit u
    obtain ⟨j,hj⟩ := horbit v
    obtain ⟨a,ha⟩ := horbit w
    letI := A.toMulAction
    have hfixed (y : Point C.toGeometric)
        (hy : ∀ t : Variety.Point T.carrierVariety,R.toMulAction.smul (T.includePoint t) y=y)
        (g : Variety.Point G) (hg : g • x = C.inclusion y) :
        ∀ t∈T.toSubgroup,t • (g • x)=g • x := by
      intro t ht
      have htR : t ∈ Set.range T.inclusion.onPoints := by rw [T.range_inclusion];exact ht
      obtain ⟨s,rfl⟩ := htR
      rw [hg]
      have hh := A.onInvariantReducedClosedSubvariety_inclusion Z hinv (T.includePoint s) y
      exact hh.symm.trans (congrArg (fun p => C.inclusion p) (hy s))
    have hinj : Function.Injective (fun y : Point C.toGeometric => C.inclusion y) := by
      intro p q hpq
      apply Subtype.ext
      exact (cancel_mono C.inclusion.hom).mp (congrArg Subtype.val hpq)
    rcases rank_one_orbit_fixedPoints_no_three hG T hT hdimT B hB x hstab g j a
      (hfixed u huf g hg) (hfixed v hvf j hj) (hfixed w hwf a ha) with h | h | h
    · exact huv (hinj (hg.symm.trans (h.trans hj)))
    · exact huw (hinj (hg.symm.trans (h.trans ha)))
    · exact hvw (hinj (hj.symm.trans (h.trans ha)))
  let O := A.orbitSubvariety x
  letI : IsClosedImmersion O.inclusion.hom := A.orbitSubvariety_isClosedImmersion x hclosed
  let e₁ := O.inclusion.hom.isClosedEmbedding.isEmbedding.toHomeomorph
  let e₂ : Set.range O.inclusion.hom ≃ₜ Set.range C.inclusion.hom :=
    Homeomorph.setCongr ((A.orbitSubvariety_range x).trans (reducedClosedSubvariety_range P Z).symm)
  let e₃ := C.inclusion.hom.isClosedEmbedding.isEmbedding.toHomeomorph.symm
  exact (e₁.trans (e₂.trans e₃)).isHomeomorph.topologicalKrullDim_eq.le.trans hCdim

/-- The original rank-one group and Borel produce the literal projective
orbit together with its dimension bound. -/
theorem exists_projective_borel_model_dimension_le_one
    (hG : Variety.IsConnected G) (T : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdimT : Variety.dimension T.carrierVariety=1)
    (B : ClosedSubgroup G) (hB : IsBorelSubgroup B) :
    ∃ (E : Type u) (_ : AddCommGroup E) (_ : Module k E) (_ : FiniteDimensional k E)
      (ρ : RationalRepresentation G E)
      (b : Module.Basis (Fin (Module.finrank k E)) k E)
      (A : MorphicAction G (projectiveSpace k E)) (x : Point (projectiveSpace k E)),
      IsRationalRepresentation ρ ∧
      (∀ (g : Variety.Point G) (p : Point (projectiveSpace k E)),
        projectiveSpacePointEquivOf b (A.toMulAction.smul g p) =
        Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
          (projectiveSpacePointEquivOf b p)) ∧
      (∀ g : Variety.Point G, A.toMulAction.smul g x=x ↔ g∈B.toSubgroup) ∧
      dimension (A.orbitSubvariety x).toGeometric ≤ 1 := by
  obtain ⟨E,hEa,hEm,hEf,ρ,b,A,x,hρ,he,hstab⟩ :=
    TorusBorelGeneration.exists_projective_action_stabilizer B
  exact ⟨E,hEa,hEm,hEf,ρ,b,A,x,hρ,he,hstab,
    projective_borel_orbit_dimension_le_one hG T hT hdimT B hB ρ hρ b A x he hstab⟩

end Theory.AlgebraicGroup.Bor1.RankOneGeometry
