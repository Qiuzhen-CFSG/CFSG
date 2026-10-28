module

public import Theory.AlgebraicGroup.Variety.ProjectiveLine
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Polynomial curves in projective space

Homogeneous polynomial coordinates with a unit coordinate define an everywhere
regular curve on the affine line. The native scheme morphism evaluates to the
literal projective point represented by those coordinates. Polynomial identity
then shows that closed sets containing the nonzero parameter values contain the
zero value too.

This supplies the affine curves in Borel, *Linear Algebraic Groups*, IV, 13.3,
without assuming the existence or the description of a cocharacter limit.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve

universe u
variable {k : Type u} [Field k] {ι : Type} [Finite ι]

def affinePoint (a : k) : Point (polynomialAffineLine k) where
  val := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))
  property := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of k) using 1
    congr 1
    ext x
    simp

def sections (p : ι → Polynomial k) :
    MvPolynomial ι k →+* Γ(Spec (.of (Polynomial k)), ⊤) :=
  (Scheme.ΓSpecIso (.of (Polynomial k))).inv.hom.comp (MvPolynomial.aeval p).toRingHom

omit [Finite ι] in
theorem irrelevant (p : ι → Polynomial k) (hp : ∃ i, IsUnit (p i)) :
    Ideal.map (sections p)
      (HomogeneousIdeal.irrelevant (projectiveGrading k ι)).toIdeal = ⊤ := by
  obtain ⟨i, hi⟩ := hp
  have hXi : MvPolynomial.X i ∈
      (HomogeneousIdeal.irrelevant (projectiveGrading k ι)).toIdeal := by
    change MvPolynomial.X i ∈ HomogeneousIdeal.irrelevant (projectiveGrading k ι)
    rw [HomogeneousIdeal.mem_irrelevant_iff]
    exact DirectSum.decompose_of_mem_ne _
      ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
        (MvPolynomial.isHomogeneous_X k i)) one_ne_zero
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem (sections p) hXi) ?_
  simpa [sections] using hi.map (Scheme.ΓSpecIso (.of (Polynomial k))).inv.hom

def curve (p : ι → Polynomial k) (hp : ∃ i, IsUnit (p i)) :
    Morphism (polynomialAffineLine k) (projectiveSpaceByCoordinates k ι) where
  hom := Proj.fromOfGlobalSections (projectiveGrading k ι) (sections p) (irrelevant p hp)
  commutes := by
    change Proj.fromOfGlobalSections (projectiveGrading k ι) (sections p) (irrelevant p hp) ≫
      (Proj.toSpecZero (projectiveGrading k ι) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (projectiveGrading k ι 0)))) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
    rw [← Category.assoc, Proj.fromOfGlobalSections_toSpecZero,
      ← SpecMap_ΓSpecIso_hom]
    simp only [← Spec.map_comp, CommRingCat.ofHom_comp]
    congr 1
    ext x
    simp [sections]

omit [Finite ι] in
theorem eval_ne_zero (p : ι → Polynomial k) (hp : ∃ i, IsUnit (p i)) (a : k) :
    (fun i => (p i).eval a) ≠ 0 := by
  obtain ⟨i, hi⟩ := hp
  intro hz
  exact (hi.map (Polynomial.evalRingHom a)).ne_zero (congr_fun hz i)

private theorem closedPoint_ideal :
    (IsLocalRing.closedPoint k).asIdeal = (⊥ : Ideal k) :=
  (Ideal.eq_bot_or_top _).resolve_right (IsLocalRing.closedPoint k).isPrime.ne_top

set_option backward.isDefEq.respectTransparency false in
theorem curve_mem_iff (p : ι → Polynomial k) (hp : ∃ i, IsUnit (p i)) (a : k)
    {f : MvPolynomial ι k} {n : ℕ} (hf : f ∈ projectiveGrading k ι n) :
    f ∈ ((curve p hp).hom ((affinePoint a).1 (IsLocalRing.closedPoint k))).asHomogeneousIdeal ↔
      MvPolynomial.eval₂Hom (RingHom.id k) (fun i => (p i).eval a) f = 0 := by
  by_cases hn : n = 0
  · subst n
    change f ∈ MvPolynomial.homogeneousSubmodule ι k 0 at hf
    rw [MvPolynomial.homogeneousSubmodule_zero, Submodule.mem_one] at hf
    obtain ⟨r, rfl⟩ := hf
    simp only [MvPolynomial.algebraMap_eq, MvPolynomial.eval₂Hom_C, RingHom.id_apply]
    constructor
    · intro hr
      by_contra hr0
      exact ((curve p hp).hom ((affinePoint a).1 (IsLocalRing.closedPoint k))).2.ne_top
        (Ideal.eq_top_of_isUnit_mem _ hr
          ((isUnit_iff_ne_zero.mpr hr0).map (MvPolynomial.C : k →+* MvPolynomial ι k)))
    · rintro rfl
      simp
  · rw [← not_iff_not]
    change f ∉ _ ↔ _ ≠ 0
    rw [← Proj.mem_basicOpen (projectiveGrading k ι) f]
    change _ ∈ Proj.basicOpen (projectiveGrading k ι) f ↔ _
    change _ ∈ (Proj.fromOfGlobalSections (projectiveGrading k ι)
      (sections p) (irrelevant p hp)) ⁻¹ᵁ Proj.basicOpen (projectiveGrading k ι) f ↔ _
    rw [Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ (Nat.pos_of_ne_zero hn) hf]
    dsimp only [sections, RingHom.comp_apply]
    rw [basicOpen_eq_of_affine]
    change (MvPolynomial.aeval p) f ∉
      (PrimeSpectrum.comap (Polynomial.evalRingHom a) (IsLocalRing.closedPoint k)).asIdeal ↔ _
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, closedPoint_ideal]
    change (Polynomial.evalRingHom a) ((MvPolynomial.aeval p) f) ≠ 0 ↔ _
    have heq : (Polynomial.evalRingHom a).comp (MvPolynomial.aeval p).toRingHom =
        MvPolynomial.eval₂Hom (RingHom.id k) (fun i => (p i).eval a) := by
      ext x <;> simp
    exact (congrArg (fun z : k => z ≠ 0) (DFunLike.congr_fun heq f)).to_iff

variable [IsAlgClosed k]

theorem curve_point (p : ι → Polynomial k) (hp : ∃ i, IsUnit (p i)) (a : k) :
    (curve p hp) (affinePoint a) =
      projectivePointOfVector (fun i => (p i).eval a) (eval_ne_zero p hp a) := by
  apply Subtype.ext
  apply ext_of_apply_closedPoint_eq (projectiveSpaceByCoordinates k ι).structureMap
    ((curve p hp) (affinePoint a)).property
    (projectivePointOfVector _ _).property
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n f hf
  rw [projectivePointOfVector_mem_iff _ _ hf]
  exact curve_mem_iff p hp a hf

/-- A closed subset of the affine line containing every nonzero rational point
contains every rational point. -/
theorem affinePoint_mem_of_nonzero {Z : Set (polynomialAffineLine k).toScheme}
    (hZ : IsClosed Z)
    (h : ∀ a : k, a ≠ 0 → (affinePoint a).1 (IsLocalRing.closedPoint k) ∈ Z)
    (a : k) : (affinePoint a).1 (IsLocalRing.closedPoint k) ∈ Z := by
  obtain ⟨S, hS⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus Z).mp hZ
  rw [hS] at h ⊢
  intro f hf
  have hzero : f = 0 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.finite_singleton (0 : k)).infinite_compl.mono
    intro t ht
    have hm := h t ht hf
    change (Polynomial.evalRingHom t) f ∈ (IsLocalRing.closedPoint k).asIdeal at hm
    rw [closedPoint_ideal] at hm
    simpa using hm
  simp [hzero]

/-- Polynomial projective curves specialize into any closed set which contains
their nonzero parameter values. -/
theorem curve_zero_mem_of_nonzero (p : ι → Polynomial k) (hp : ∃ i, IsUnit (p i))
    {Z : Set (projectiveSpaceByCoordinates k ι).toScheme} (hZ : IsClosed Z)
    (h : ∀ a : k, a ≠ 0 →
      ((curve p hp) (affinePoint a)).1 (IsLocalRing.closedPoint k) ∈ Z) :
    ((curve p hp) (affinePoint 0)).1 (IsLocalRing.closedPoint k) ∈ Z := by
  exact affinePoint_mem_of_nonzero (hZ.preimage (curve p hp).hom.continuous) h 0

end Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve
