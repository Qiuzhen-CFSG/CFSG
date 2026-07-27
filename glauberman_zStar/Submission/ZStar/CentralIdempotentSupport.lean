import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.AlgebraTower
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Central idempotents and support on involutions

This file isolates the algebraic trace calculation behind weak block
orthogonality.  The key point is that a finite module which is free over the
group algebra of a cyclic subgroup is a sum of regular modules.  Consequently
every nonidentity element of that subgroup has trace zero.
-/

noncomputable section

open scoped BigOperators

open Module
open CategoryTheory

namespace Submission.ZStar

namespace CentralIdempotentSupport

universe u v w

attribute [local instance] Fintype.ofFinite

/-- The group algebra of a two-element commutative group over a local ring in
which `2` is a nonunit is local.  This is the integral `C₂`-locality input
used below. -/
theorem isLocalRing_monoidAlgebra_of_card_two
    {R C : Type*} [CommRing R] [IsLocalRing R] [CommGroup C]
    (h2 : ¬ IsUnit (2 : R))
    (hC : Nat.card C = 2) :
    IsLocalRing (MonoidAlgebra R C) := by
  classical
  obtain ⟨c, hc, hc_unique⟩ := (Nat.card_eq_two_iff' (1 : C)).mp hC
  have hall (x : C) : x = 1 ∨ x = c := by
    by_cases hx : x = 1
    · exact Or.inl hx
    · exact Or.inr (hc_unique x hx)
  have hc2 : c * c = 1 := by
    rcases hall (c * c) with h | h
    · exact h
    · exfalso
      apply hc
      apply mul_left_cancel (a := c)
      simpa using h
  have isUnit_pair (a b : R) (hab : IsUnit (a + b)) :
      IsUnit (MonoidAlgebra.single (1 : C) a +
        MonoidAlgebra.single c b) := by
    have h2b : ¬ IsUnit (2 * b) := by
      intro h
      exact h2 (isUnit_of_mul_isUnit_left h)
    have hamb : IsUnit (a - b) := by
      by_contra h
      have hn := IsLocalRing.nonunits_add h h2b
      apply hn
      have heq : a - b + 2 * b = a + b := by ring
      rw [heq]
      exact hab
    have hdet : IsUnit (a ^ 2 - b ^ 2) := by
      rw [sq_sub_sq]
      exact hab.mul hamb
    let x : MonoidAlgebra R C :=
      MonoidAlgebra.single (1 : C) a + MonoidAlgebra.single c b
    let y : MonoidAlgebra R C :=
      MonoidAlgebra.single (1 : C) a - MonoidAlgebra.single c b
    have hxy : x * y =
        algebraMap R (MonoidAlgebra R C) (a ^ 2 - b ^ 2) := by
      dsimp [x, y]
      rw [add_mul, mul_sub, mul_sub, MonoidAlgebra.single_mul_single,
        MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single,
        MonoidAlgebra.single_mul_single]
      simp [hc2]
      ext z
      change
        (Finsupp.single (1 : C) (a * a) z -
            Finsupp.single c (a * b) z) +
          (Finsupp.single c (b * a) z -
            Finsupp.single (1 : C) (b * b) z) =
          Finsupp.single (1 : C) (a ^ 2) z -
            Finsupp.single (1 : C) (b ^ 2) z
      rcases hall z with rfl | rfl
      · simp [hc]
        ring
      · simp [hc]
        ring
    apply isUnit_of_mul_isUnit_left (y := y)
    rw [hxy]
    exact hdet.map (algebraMap R (MonoidAlgebra R C))
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro f
  let a := f 1
  let b := f c
  have hf : f = MonoidAlgebra.single (1 : C) a +
      MonoidAlgebra.single c b := by
    ext x
    rcases hall x with rfl | rfl <;> simp [a, b, hc]
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (a + b) with hab | hab
  · rw [hf]
    exact Or.inl (isUnit_pair a b hab)
  · right
    rw [hf]
    have hrewrite :
        (1 - (MonoidAlgebra.single (1 : C) a +
          MonoidAlgebra.single c b) : MonoidAlgebra R C) =
        MonoidAlgebra.single (1 : C) (1 - a) +
          MonoidAlgebra.single c (-b) := by
      ext x
      change
        MonoidAlgebra.single (1 : C) 1 x -
            (MonoidAlgebra.single (1 : C) a x +
              MonoidAlgebra.single c b x) =
          MonoidAlgebra.single (1 : C) (1 - a) x +
            MonoidAlgebra.single c (-b) x
      rcases hall x with rfl | rfl
      · simp [hc]
      · simp [hc]
    rw [hrewrite]
    apply isUnit_pair
    convert hab using 1
    ring

/-- Left multiplication by a nonidentity group element has trace zero on the
group algebra. -/
theorem trace_mulLeft_of_ne_one
    {R : Type u} {C : Type v} [CommRing R] [CommGroup C] [Finite C]
    (g : C) (hg : g ≠ 1) :
    LinearMap.trace R (MonoidAlgebra R C)
        (LinearMap.mulLeft R (MonoidAlgebra.of R C g)) = 0 := by
  classical
  let b : Basis C R (MonoidAlgebra R C) := Finsupp.basisSingleOne
  rw [LinearMap.trace_eq_matrix_trace R b, Matrix.trace]
  apply Finset.sum_eq_zero
  intro i _hi
  change Algebra.leftMulMatrix b (MonoidAlgebra.of R C g) i i = 0
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  change (MonoidAlgebra.single g 1 * MonoidAlgebra.single i 1 :
      MonoidAlgebra R C) i = 0
  simp [hg]

/-- A nonidentity element has trace zero on every finite free module over its
group algebra.  This is the algebraic form of "a free character vanishes away
from the identity". -/
theorem trace_lsmul_of_free_groupAlgebra
    {R : Type u} {C : Type v} {M : Type w}
    [CommRing R] [CommGroup C] [Finite C]
    [AddCommGroup M] [Module R M] [Module (MonoidAlgebra R C) M]
    [IsScalarTower R (MonoidAlgebra R C) M]
    [Module.Free (MonoidAlgebra R C) M]
    [Module.Finite (MonoidAlgebra R C) M]
    (g : C) (hg : g ≠ 1) :
    LinearMap.trace R M
        ((LinearMap.lsmul (MonoidAlgebra R C) M
          (MonoidAlgebra.of R C g)).restrictScalars R) = 0 := by
  classical
  let bR : Basis C R (MonoidAlgebra R C) := Finsupp.basisSingleOne
  let bM := Module.Free.chooseBasis (MonoidAlgebra R C) M
  rw [LinearMap.trace_eq_matrix_trace R (bR.smulTower' bM), Matrix.trace]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ _hij
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply,
    Basis.smulTower'_repr, Basis.smulTower'_apply,
    LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
  simp only [map_smul, Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply, if_pos, smul_eq_mul, mul_one]
  change bR.repr
      ((MonoidAlgebra.of R C g) * bR j) j = 0
  change (MonoidAlgebra.single g 1 * MonoidAlgebra.single j 1 :
      MonoidAlgebra R C) j = 0
  simp [hg]

/-- Representation-theoretic form of `trace_lsmul_of_free_groupAlgebra`. -/
theorem trace_representation_of_free_asModule
    {R : Type u} {C : Type v} {V : Type w}
    [CommRing R] [CommGroup C] [Finite C]
    [AddCommGroup V] [Module R V]
    (rho : Representation R C V)
    [Module.Free (MonoidAlgebra R C) rho.asModule]
    [Module.Finite (MonoidAlgebra R C) rho.asModule]
    (g : C) (hg : g ≠ 1) :
    LinearMap.trace R V (rho g) = 0 := by
  let f : rho.asModule →ₗ[R] rho.asModule :=
    (LinearMap.lsmul (MonoidAlgebra R C) rho.asModule
      (MonoidAlgebra.of R C g)).restrictScalars R
  have hf : rho.asModuleEquiv.conj f = rho g := by
    ext x
    simp [f, LinearEquiv.conj_apply_apply]
    rfl
  have h := trace_lsmul_of_free_groupAlgebra
    (R := R) (C := C) (M := rho.asModule) g hg
  calc
    LinearMap.trace R V (rho g) =
        LinearMap.trace R V (rho.asModuleEquiv.conj f) := by rw [hf]
    _ = LinearMap.trace R rho.asModule f := LinearMap.trace_conj' f rho.asModuleEquiv
    _ = 0 := h

/-- Over a local group algebra, finite projective representations vanish on
nonidentity elements.  The only input beyond projectivity is the standard
fact that finite flat modules over local rings are free. -/
theorem trace_representation_of_projective_asModule
    {R : Type u} {C : Type v} {V : Type w}
    [CommRing R] [CommGroup C] [Finite C]
    [AddCommGroup V] [Module R V]
    (rho : Representation R C V)
    [IsLocalRing (MonoidAlgebra R C)]
    [Module.Projective (MonoidAlgebra R C) rho.asModule]
    [Module.Finite (MonoidAlgebra R C) rho.asModule]
    (g : C) (hg : g ≠ 1) :
    LinearMap.trace R V (rho g) = 0 := by
  letI : Module.Free (MonoidAlgebra R C) rho.asModule :=
    Module.free_of_flat_of_isLocalRing
  exact trace_representation_of_free_asModule rho g hg

/-- The coefficients of a central group-algebra element are constant on
conjugacy classes. -/
theorem coeff_conj_eq_of_mem_center
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (e : MonoidAlgebra R G) (he : e ∈ Set.center (MonoidAlgebra R G))
    (x y : G) :
    e (x * y * x⁻¹) = e y := by
  have hcomm := Semigroup.mem_center_iff.mp he (MonoidAlgebra.of R G x)
  have h := congrArg (fun z : MonoidAlgebra R G ↦ z (x * y)) hcomm
  simpa [MonoidAlgebra.of_apply, mul_assoc] using h.symm

/-- The trace of `x ↦ g * x * e` on the regular module is the group order
times the coefficient of `g⁻¹` in the central element `e`. -/
theorem trace_mulLeft_comp_mulRight
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (e : MonoidAlgebra R G) (he : e ∈ Set.center (MonoidAlgebra R G))
    (g : G) :
    LinearMap.trace R (MonoidAlgebra R G)
        ((LinearMap.mulLeft R (MonoidAlgebra.of R G g)).comp
          (LinearMap.mulRight R e)) =
      (Nat.card G : R) * e g⁻¹ := by
  classical
  let b : Basis G R (MonoidAlgebra R G) := Finsupp.basisSingleOne
  rw [LinearMap.trace_eq_matrix_trace R b, Matrix.trace]
  have hdiag : ∀ x : G,
      ((LinearMap.toMatrix b b)
        ((LinearMap.mulLeft R (MonoidAlgebra.of R G g)).comp
          (LinearMap.mulRight R e))).diag x = e g⁻¹ := by
    intro x
    simp only [Matrix.diag_apply, LinearMap.toMatrix_apply,
      LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    change (MonoidAlgebra.single g 1 *
      (MonoidAlgebra.single x 1 * e) : MonoidAlgebra R G) x = e g⁻¹
    rw [← mul_assoc, MonoidAlgebra.single_mul_single]
    simp only [one_mul]
    rw [MonoidAlgebra.single_mul_apply]
    simpa [mul_assoc] using
      coeff_conj_eq_of_mem_center e he x⁻¹ g⁻¹
  simp_rw [hdiag]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  congr 1
  exact congrArg (fun n : ℕ ↦ (n : R))
    (Fintype.card_eq_nat_card : Fintype.card G = Nat.card G)

/-- If `p` is an idempotent commuting with `f`, the trace of `f ∘ p` is
the trace of `f` on the image of `p`. -/
theorem trace_comp_idempotent_eq_trace_range
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M]
    (p f : M →ₗ[R] M) (hp : IsIdempotentElem p)
    [Module.Free R (LinearMap.range p)]
    [Module.Finite R (LinearMap.range p)]
    [Module.Free R (LinearMap.ker p)]
    [Module.Finite R (LinearMap.ker p)]
    (hcomm : f.comp p = p.comp f) :
    LinearMap.trace R M (f.comp p) =
      LinearMap.trace R (LinearMap.range p)
        (f.restrict (by
          rintro _ ⟨x, rfl⟩
          refine ⟨f x, ?_⟩
          simpa [LinearMap.comp_apply] using
            congrArg (fun q : M →ₗ[R] M ↦ q x) hcomm.symm)) := by
  let hmap : LinearMap.range p ≤ (LinearMap.range p).comap f := by
    rintro _ ⟨x, rfl⟩
    refine ⟨f x, ?_⟩
    simpa [LinearMap.comp_apply] using
      congrArg (fun q : M →ₗ[R] M ↦ q x) hcomm.symm
  let fp : LinearMap.range p →ₗ[R] LinearMap.range p := f.restrict hmap
  let E := (LinearMap.range p).prodEquivOfIsCompl (LinearMap.ker p)
    (LinearMap.IsIdempotentElem.isCompl hp)
  have hconj : E.symm.conj (f.comp p) = LinearMap.prodMap fp 0 := by
    apply LinearMap.ext
    rintro ⟨x, y⟩
    apply E.injective
    simp only [LinearEquiv.conj_apply_apply, LinearEquiv.apply_symm_apply,
      LinearMap.prodMap_apply, E, fp]
    change f (p (x + y)) = f x + 0
    rw [map_add,
      (LinearMap.IsIdempotentElem.isProj_range p hp).map_id x x.2,
      LinearMap.mem_ker.mp y.2]
    simp
  calc
    LinearMap.trace R M (f.comp p) =
        LinearMap.trace R (LinearMap.range p × LinearMap.ker p)
          (E.symm.conj (f.comp p)) := by
            symm
            exact LinearMap.trace_conj' (f.comp p) E.symm
    _ = LinearMap.trace R (LinearMap.range p × LinearMap.ker p)
          (LinearMap.prodMap fp 0) := by rw [hconj]
    _ = LinearMap.trace R (LinearMap.range p) fp := by
      rw [LinearMap.trace_prodMap']
      simp

/-- The range of an idempotent on a projective module is projective. -/
theorem projective_range_of_isIdempotentElem
    {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Projective R M]
    (p : M →ₗ[R] M) (hp : IsIdempotentElem p) :
    Module.Projective R (LinearMap.range p) := by
  let hproj := LinearMap.IsIdempotentElem.isProj_range p hp
  apply Module.Projective.of_split (LinearMap.range p).subtype hproj.codRestrict
  ext x
  simp [LinearMap.comp_apply]

/-- Over a local ring, the image of an idempotent on a finite projective
module is free. -/
theorem free_range_of_isIdempotentElem_of_isLocalRing
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Projective R M] [Module.Finite R M]
    (p : M →ₗ[R] M) (hp : IsIdempotentElem p) :
    Module.Free R (LinearMap.range p) := by
  letI : Module.Projective R (LinearMap.range p) :=
    projective_range_of_isIdempotentElem p hp
  exact Module.free_of_flat_of_isLocalRing

/-- Over a local ring, the kernel of an idempotent on a finite projective
module is free as well. -/
theorem free_ker_of_isIdempotentElem_of_isLocalRing
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Projective R M] [Module.Finite R M]
    (p : M →ₗ[R] M) (hp : IsIdempotentElem p) :
    Module.Free R (LinearMap.ker p) := by
  rw [LinearMap.IsIdempotentElem.ker_eq_range hp]
  exact free_range_of_isIdempotentElem_of_isLocalRing
    (LinearMap.id - p) hp.one_sub

/-- The right ideal cut out by `e`, viewed only as an `R`-submodule. -/
abbrev rightIdeal
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (e : MonoidAlgebra R G) : Submodule R (MonoidAlgebra R G) :=
  LinearMap.range (LinearMap.mulRight R e)

/-- Left multiplication by `g` on the right ideal generated by `e`. -/
def rightIdealAction
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (e : MonoidAlgebra R G) (g : G) :
    rightIdeal R e →ₗ[R] rightIdeal R e :=
  (LinearMap.mulLeft R (MonoidAlgebra.of R G g)).restrict (by
    rintro _ ⟨x, rfl⟩
    refine ⟨MonoidAlgebra.of R G g * x, ?_⟩
    simp [mul_assoc])

@[simp]
theorem rightIdealAction_apply
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (e : MonoidAlgebra R G) (g : G) (x : rightIdeal R e) :
    (rightIdealAction R e g x : MonoidAlgebra R G) =
      MonoidAlgebra.of R G g * (x : MonoidAlgebra R G) :=
  rfl

/-- The block/right-ideal summand of the regular representation. -/
def rightIdealRepresentation
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (e : MonoidAlgebra R G) : Representation R G (rightIdeal R e) where
  toFun := rightIdealAction R e
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [mul_assoc]

/-- Restriction of the right-ideal representation along a monoid homomorphism. -/
abbrev restrictedRightIdealRepresentation
    (R : Type u) {C : Type v} {G : Type w}
    [CommRing R] [Monoid C] [Group G]
    (e : MonoidAlgebra R G) (phi : C →* G) :
    Representation R C (rightIdeal R e) :=
  (rightIdealRepresentation R e).comp phi

/-- Restriction of the ambient left regular representation to a subgroup. -/
abbrev restrictedLeftRegularRepresentation
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (S : Subgroup G) : Representation R S (MonoidAlgebra R G) :=
  (Representation.leftRegular R G).comp S.subtype

/-- The free representation on one generator is the left regular
representation.  We use this version because Mathlib's global projectivity
instance for `leftRegular` unnecessarily puts the coefficient ring and group
in the same universe. -/
private noncomputable def freePUnitEquivLeftRegular
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    (Representation.free R G PUnit).Equiv
      (Representation.leftRegular R G) :=
  Representation.Equiv.mk
    (Finsupp.uniqueLinearEquiv R (G →₀ R) PUnit.unit) (by
      intro g
      ext f x
      simp [Representation.finsupp_apply])

private noncomputable def freePUnitIsoLeftRegular
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    Rep.free R G PUnit ≅ Rep.leftRegular R G :=
  Rep.mkIso (freePUnitEquivLeftRegular R G)

/-- Restriction of the left regular representation to a subgroup is
projective over the subgroup algebra.  Categorically, restriction preserves
projectives because it is left adjoint to coinduction. -/
theorem projective_restrictedLeftRegular_asModule
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (S : Subgroup G) :
    Module.Projective (MonoidAlgebra R S)
      (restrictedLeftRegularRepresentation R S).asModule := by
  let X : Rep R G := Rep.leftRegular R G
  let Y : Rep R S := Rep.res S.subtype X
  letI : Projective X :=
    Projective.of_iso (freePUnitIsoLeftRegular R G) inferInstance
  letI : Projective Y := (Rep.resFunctor S.subtype).projective_obj X
  change Module.Projective (MonoidAlgebra R S) Y.ρ.asModule
  exact ModuleCat.projective_of_module_projective
    (Rep.toModuleMonoidAlgebra.obj Y)

/-- The left regular action agrees with multiplication in the group
algebra. -/
theorem leftRegular_apply_eq_mul
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (g : G) (x : MonoidAlgebra R G) :
    Representation.leftRegular R G g x =
      MonoidAlgebra.of R G g * x := by
  ext y
  simp [Representation.ofMulAction_apply,
    MonoidAlgebra.single_mul_apply]

/-- Inclusion of the idempotent right ideal into the restricted regular
representation. -/
def rightIdealInclusionIntertwiningMap
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (e : MonoidAlgebra R G) (S : Subgroup G) :
    (restrictedRightIdealRepresentation R e S.subtype).IntertwiningMap
      (restrictedLeftRegularRepresentation R S) where
  toLinearMap := (rightIdeal R e).subtype
  isIntertwining' s := by
    apply LinearMap.ext
    intro x
    exact (leftRegular_apply_eq_mul (R := R) (G := G) (s : G)
      (x : MonoidAlgebra R G)).symm

/-- Right multiplication by `e`, with codomain restricted to its range, is
an intertwining projection from the restricted regular representation. -/
def rightIdealProjectionIntertwiningMap
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (e : MonoidAlgebra R G) (S : Subgroup G) :
    (restrictedLeftRegularRepresentation R S).IntertwiningMap
      (restrictedRightIdealRepresentation R e S.subtype) where
  toLinearMap := (LinearMap.mulRight R e).codRestrict (rightIdeal R e)
    (fun x ↦ ⟨x, rfl⟩)
  isIntertwining' s := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (show MonoidAlgebra R G from
        Representation.leftRegular R G (s : G) x) * e =
      MonoidAlgebra.of R G (s : G) * (x * e)
    rw [leftRegular_apply_eq_mul]
    exact mul_assoc _ _ _

/-- The inclusion above, regarded as a linear map over the subgroup
algebra. -/
abbrev rightIdealInclusionAsModule
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (e : MonoidAlgebra R G) (S : Subgroup G) :
    (restrictedRightIdealRepresentation R e S.subtype).asModule →ₗ[MonoidAlgebra R S]
      (restrictedLeftRegularRepresentation R S).asModule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule _ _)
    (rightIdealInclusionIntertwiningMap R e S)

/-- The right-multiplication projection above, regarded as a linear map over
the subgroup algebra. -/
abbrev rightIdealProjectionAsModule
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (e : MonoidAlgebra R G) (S : Subgroup G) :
    (restrictedLeftRegularRepresentation R S).asModule →ₗ[MonoidAlgebra R S]
      (restrictedRightIdealRepresentation R e S.subtype).asModule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule _ _)
    (rightIdealProjectionIntertwiningMap R e S)

/-- For idempotent `e`, right multiplication splits the inclusion of its
right ideal, now over the subgroup algebra. -/
theorem rightIdealProjection_comp_inclusion
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    (S : Subgroup G) :
    (rightIdealProjectionAsModule R e S).comp
        (rightIdealInclusionAsModule R e S) = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, hx⟩
  apply Subtype.ext
  rcases hx with ⟨y, hy⟩
  change x * e = x
  rw [← hy]
  change (y * e) * e = y * e
  rw [mul_assoc, heidem]

/-- The right-ideal summand of the regular representation remains projective
after restriction to any subgroup. -/
theorem projective_restrictedRightIdeal_asModule
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    (S : Subgroup G) :
    Module.Projective (MonoidAlgebra R S)
      (restrictedRightIdealRepresentation R e S.subtype).asModule := by
  letI : Module.Projective (MonoidAlgebra R S)
      (restrictedLeftRegularRepresentation R S).asModule :=
    projective_restrictedLeftRegular_asModule S
  exact Module.Projective.of_split
    (rightIdealInclusionAsModule R e S)
    (rightIdealProjectionAsModule R e S)
    (rightIdealProjection_comp_inclusion e heidem S)

/-- If the ambient group is finite, the restricted right-ideal summand is a
finite module over every subgroup algebra. -/
theorem finite_restrictedRightIdeal_asModule
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    (S : Subgroup G) :
    Module.Finite (MonoidAlgebra R S)
      (restrictedRightIdealRepresentation R e S.subtype).asModule := by
  letI : Module.Finite R
      (restrictedLeftRegularRepresentation R S).asModule := inferInstance
  letI : Module.Finite (MonoidAlgebra R S)
      (restrictedLeftRegularRepresentation R S).asModule :=
    Module.Finite.of_restrictScalars_finite R (MonoidAlgebra R S)
      (restrictedLeftRegularRepresentation R S).asModule
  apply Module.Finite.of_surjective (rightIdealProjectionAsModule R e S)
  intro x
  refine ⟨rightIdealInclusionAsModule R e S x, ?_⟩
  have h := LinearMap.congr_fun
    (rightIdealProjection_comp_inclusion e heidem S) x
  simpa [LinearMap.comp_apply] using h

/-- For an idempotent `e`, the trace on its right-ideal summand equals the
trace of left multiplication followed by the ambient projection `x ↦ x * e`. -/
theorem trace_mulLeft_comp_mulRight_eq_trace_rightIdeal
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    [Module.Free R (rightIdeal R e)]
    [Module.Finite R (rightIdeal R e)]
    [Module.Free R (LinearMap.ker (LinearMap.mulRight R e))]
    [Module.Finite R (LinearMap.ker (LinearMap.mulRight R e))]
    (g : G) :
    LinearMap.trace R (MonoidAlgebra R G)
        ((LinearMap.mulLeft R (MonoidAlgebra.of R G g)).comp
          (LinearMap.mulRight R e)) =
      LinearMap.trace R (rightIdeal R e) (rightIdealAction R e g) := by
  have hp : IsIdempotentElem (LinearMap.mulRight R e) := by
    change (LinearMap.mulRight R e).comp (LinearMap.mulRight R e) =
      LinearMap.mulRight R e
    rw [← LinearMap.mulRight_mul, heidem]
  have hcomm :
      (LinearMap.mulLeft R (MonoidAlgebra.of R G g)).comp
          (LinearMap.mulRight R e) =
        (LinearMap.mulRight R e).comp
          (LinearMap.mulLeft R (MonoidAlgebra.of R G g)) := by
    ext x
    simp [LinearMap.comp_apply, mul_assoc]
  simpa only [rightIdeal, rightIdealAction] using
    trace_comp_idempotent_eq_trace_range
      (LinearMap.mulRight R e)
      (LinearMap.mulLeft R (MonoidAlgebra.of R G g)) hp hcomm

/-- The coefficient formula can be read directly from the right-ideal
summand's trace. -/
theorem trace_rightIdealAction_eq_card_mul_coeff
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G))
    [Module.Free R (rightIdeal R e)]
    [Module.Finite R (rightIdeal R e)]
    [Module.Free R (LinearMap.ker (LinearMap.mulRight R e))]
    [Module.Finite R (LinearMap.ker (LinearMap.mulRight R e))]
    (g : G) :
    LinearMap.trace R (rightIdeal R e) (rightIdealAction R e g) =
      (Nat.card G : R) * e g⁻¹ := by
  rw [← trace_mulLeft_comp_mulRight_eq_trace_rightIdeal e heidem g,
    trace_mulLeft_comp_mulRight e hecenter g]

/-- In a characteristic-zero domain, vanishing of the right-ideal trace
forces the corresponding central-idempotent coefficient to vanish. -/
theorem coeff_inv_eq_zero_of_trace_rightIdealAction_eq_zero
    {R : Type u} {G : Type v} [CommRing R] [IsDomain R] [CharZero R]
    [Group G] [Finite G]
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G))
    [Module.Free R (rightIdeal R e)]
    [Module.Finite R (rightIdeal R e)]
    [Module.Free R (LinearMap.ker (LinearMap.mulRight R e))]
    [Module.Finite R (LinearMap.ker (LinearMap.mulRight R e))]
    (g : G)
    (htrace : LinearMap.trace R (rightIdeal R e) (rightIdealAction R e g) = 0) :
    e g⁻¹ = 0 := by
  have hmul : (Nat.card G : R) * e g⁻¹ = 0 := by
    rw [← trace_rightIdealAction_eq_card_mul_coeff e heidem hecenter g]
    exact htrace
  rcases mul_eq_zero.mp hmul with hcard | hcoeff
  · have hcard' : (Nat.card G : R) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := G)).ne'
    exact (hcard' hcard).elim
  · exact hcoeff

/-- A central idempotent has zero coefficient at the image of a nonidentity
element whenever its regular summand restricts projectively to a finite
commutative subgroup whose group algebra is local.  This is the precise
projective/free bridge used for an involution subgroup. -/
theorem coeff_inv_eq_zero_of_projective_restriction
    {R : Type u} {C : Type v} {G : Type w}
    [CommRing R] [IsDomain R] [CharZero R]
    [CommGroup C] [Finite C] [Group G] [Finite G]
    (phi : C →* G) (c : C) (hc : c ≠ 1)
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G))
    [Module.Free R (rightIdeal R e)]
    [Module.Finite R (rightIdeal R e)]
    [Module.Free R (LinearMap.ker (LinearMap.mulRight R e))]
    [Module.Finite R (LinearMap.ker (LinearMap.mulRight R e))]
    [IsLocalRing (MonoidAlgebra R C)]
    [Module.Projective (MonoidAlgebra R C)
      (restrictedRightIdealRepresentation R e phi).asModule]
    [Module.Finite (MonoidAlgebra R C)
      (restrictedRightIdealRepresentation R e phi).asModule] :
    e (phi c)⁻¹ = 0 := by
  apply coeff_inv_eq_zero_of_trace_rightIdealAction_eq_zero
    e heidem hecenter (phi c)
  simpa [rightIdealRepresentation] using
    trace_representation_of_projective_asModule
      (restrictedRightIdealRepresentation R e phi) c hc

/-- Local-base-ring form of `coeff_inv_eq_zero_of_projective_restriction`.
The freeness of the idempotent summand and its complement over `R` is now a
consequence rather than an input. -/
theorem coeff_inv_eq_zero_of_projective_restriction_of_local
    {R : Type u} {C : Type v} {G : Type w}
    [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R]
    [CommGroup C] [Finite C] [Group G] [Finite G]
    (phi : C →* G) (c : C) (hc : c ≠ 1)
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G))
    [IsLocalRing (MonoidAlgebra R C)]
    [Module.Projective (MonoidAlgebra R C)
      (restrictedRightIdealRepresentation R e phi).asModule]
    [Module.Finite (MonoidAlgebra R C)
      (restrictedRightIdealRepresentation R e phi).asModule] :
    e (phi c)⁻¹ = 0 := by
  let p : MonoidAlgebra R G →ₗ[R] MonoidAlgebra R G := LinearMap.mulRight R e
  have hp : IsIdempotentElem p := by
    change (LinearMap.mulRight R e).comp (LinearMap.mulRight R e) =
      LinearMap.mulRight R e
    rw [← LinearMap.mulRight_mul, heidem]
  letI : Module.Free R (rightIdeal R e) :=
    free_range_of_isIdempotentElem_of_isLocalRing p hp
  letI : Module.Finite R (rightIdeal R e) := inferInstance
  letI : Module.Free R (LinearMap.ker (LinearMap.mulRight R e)) :=
    free_ker_of_isIdempotentElem_of_isLocalRing p hp
  letI : Module.Finite R (LinearMap.ker (LinearMap.mulRight R e)) := by
    change Module.Finite R (LinearMap.ker p)
    rw [LinearMap.IsIdempotentElem.ker_eq_range hp]
    infer_instance
  exact coeff_inv_eq_zero_of_projective_restriction
    phi c hc e heidem hecenter

/-- Order-two specialization of
`coeff_inv_eq_zero_of_projective_restriction`.  In applications `C` is a
fixed concrete model of the cyclic group of order two and `c` its generator. -/
theorem coeff_involution_eq_zero_of_projective_restriction
    {R : Type u} {C : Type v} {G : Type w}
    [CommRing R] [IsDomain R] [CharZero R]
    [CommGroup C] [Finite C] [Group G] [Finite G]
    (phi : C →* G) (c : C) (hc : c ≠ 1)
    (s : G) (hphi : phi c = s) (hsq : s * s = 1)
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G))
    [Module.Free R (rightIdeal R e)]
    [Module.Finite R (rightIdeal R e)]
    [Module.Free R (LinearMap.ker (LinearMap.mulRight R e))]
    [Module.Finite R (LinearMap.ker (LinearMap.mulRight R e))]
    [IsLocalRing (MonoidAlgebra R C)]
    [Module.Projective (MonoidAlgebra R C)
      (restrictedRightIdealRepresentation R e phi).asModule]
    [Module.Finite (MonoidAlgebra R C)
      (restrictedRightIdealRepresentation R e phi).asModule] :
    e s = 0 := by
  have h := coeff_inv_eq_zero_of_projective_restriction
    phi c hc e heidem hecenter
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hsq
  simpa [hphi, hs_inv] using h

/-- Fully local order-two form.  Its remaining hypotheses are exactly the two
restriction facts: the cyclic group algebra is local, and the restricted
block-regular summand is finite projective over it. -/
theorem coeff_involution_eq_zero_of_projective_restriction_of_local
    {R : Type u} {C : Type v} {G : Type w}
    [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R]
    [CommGroup C] [Finite C] [Group G] [Finite G]
    (phi : C →* G) (c : C) (hc : c ≠ 1)
    (s : G) (hphi : phi c = s) (hsq : s * s = 1)
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G))
    [IsLocalRing (MonoidAlgebra R C)]
    [Module.Projective (MonoidAlgebra R C)
      (restrictedRightIdealRepresentation R e phi).asModule]
    [Module.Finite (MonoidAlgebra R C)
      (restrictedRightIdealRepresentation R e phi).asModule] :
    e s = 0 := by
  have h := coeff_inv_eq_zero_of_projective_restriction_of_local
    phi c hc e heidem hecenter
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hsq
  simpa [hphi, hs_inv] using h

/-- A central idempotent over a characteristic-zero local domain in which
`2` is a nonunit has zero coefficient at every nontrivial involution.

This is the unconditional support theorem needed for weak block
orthogonality: the order-two subgroup algebra is local, restriction of the
regular module is projective, and the idempotent right-ideal summand is a
finite split summand. -/
theorem coeff_involution_eq_zero
    {R : Type u} {G : Type v}
    [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R]
    [Group G] [Finite G]
    (h2 : ¬ IsUnit (2 : R))
    (s : G) (hsne : s ≠ 1) (hsq : s * s = 1)
    (e : MonoidAlgebra R G) (heidem : IsIdempotentElem e)
    (hecenter : e ∈ Set.center (MonoidAlgebra R G)) :
    e s = 0 := by
  have hsord : orderOf s = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime (p := 2)
    · rw [pow_two, hsq]
    · exact hsne
  let S : Subgroup G := Subgroup.zpowers s
  have hScard : Nat.card S = 2 := by
    dsimp [S]
    rw [Nat.card_zpowers, hsord]
  letI : Finite S := Nat.finite_of_card_ne_zero (by omega)
  letI : CommGroup S := IsCyclic.commGroup
  let c : S := ⟨s, Subgroup.mem_zpowers s⟩
  have hc : c ≠ 1 := by
    intro h
    apply hsne
    exact congrArg Subtype.val h
  letI : IsLocalRing (MonoidAlgebra R S) :=
    isLocalRing_monoidAlgebra_of_card_two h2 hScard
  letI : Module.Projective (MonoidAlgebra R S)
      (restrictedRightIdealRepresentation R e S.subtype).asModule :=
    projective_restrictedRightIdeal_asModule e heidem S
  letI : Module.Finite (MonoidAlgebra R S)
      (restrictedRightIdealRepresentation R e S.subtype).asModule :=
    finite_restrictedRightIdeal_asModule e heidem S
  exact coeff_involution_eq_zero_of_projective_restriction_of_local
    (R := R) (C := S) (G := G) S.subtype c hc s rfl hsq
      e heidem hecenter

end CentralIdempotentSupport

end Submission.ZStar
