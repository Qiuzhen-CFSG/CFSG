import Submission.ZStar.ExactRelativeTrace
import Submission.ZStar.HigmanScratch
import Submission.ZStar.CentralIdempotentSupport
import Mathlib.RepresentationTheory.Intertwining

noncomputable section

namespace Submission.ZStar
namespace LeftIdealHigman

universe u v w

attribute [local instance] Fintype.ofFinite

lemma conjugation_eq_group_elements_mul
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (z : G) (a : MonoidAlgebra R G) :
    BrauerKernelRelativeTrace.conjugation R z a =
      MonoidAlgebra.of R G z * a * MonoidAlgebra.of R G z⁻¹ := by
  ext x
  rw [BrauerKernelRelativeTrace.conjugation_apply]
  simp [MonoidAlgebra.mul_single_apply, MonoidAlgebra.single_mul_apply,
    mul_assoc]

theorem commute_zpowers_of_conjugation_fixed
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (z : G) (hzne : z ≠ 1) (hz : z * z = 1)
    (f : MonoidAlgebra R G)
    (hfinv : BrauerKernelRelativeTrace.conjugation R z f = f) :
    ∀ s : Subgroup.zpowers z,
      Commute f (MonoidAlgebra.of R G ((Subgroup.zpowers z).subtype s)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzord : orderOf z = 2 := by
    apply orderOf_eq_prime (p := 2)
    · rw [pow_two, hz]
    · exact hzne
  let S : Subgroup G := Subgroup.zpowers z
  have hScard : Nat.card S = 2 := by
    dsimp [S]
    rw [Nat.card_zpowers, hzord]
  let zS : S := ⟨z, Subgroup.mem_zpowers z⟩
  have hzSne : zS ≠ 1 := by
    intro h
    apply hzne
    exact congrArg Subtype.val h
  obtain ⟨q, hq, hunique⟩ := (Nat.card_eq_two_iff' (1 : S)).mp hScard
  have hall (s : S) : s = 1 ∨ s = zS := by
    by_cases hs : s = 1
    · exact Or.inl hs
    · exact Or.inr ((hunique s hs).trans (hunique zS hzSne).symm)
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hconjmul :
      MonoidAlgebra.of R G z * f * MonoidAlgebra.of R G z = f := by
    have h := hfinv
    rw [conjugation_eq_group_elements_mul, hzinv] at h
    exact h
  have hcommz : Commute f (MonoidAlgebra.of R G z) := by
    rw [commute_iff_eq]
    calc
      f * MonoidAlgebra.of R G z =
          (MonoidAlgebra.of R G z * f * MonoidAlgebra.of R G z) *
            MonoidAlgebra.of R G z := by rw [hconjmul]
      _ = MonoidAlgebra.of R G z * f *
          (MonoidAlgebra.of R G z * MonoidAlgebra.of R G z) := by ac_rfl
      _ = MonoidAlgebra.of R G z * f := by
        rw [← map_mul, hz, map_one, mul_one]
  intro s
  change Commute f (MonoidAlgebra.of R G (s : G))
  rcases hall s with rfl | rfl
  · change Commute f (1 : MonoidAlgebra R G)
    exact Commute.one_right f
  · exact hcommz

abbrev leftIdeal
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) : Submodule R (MonoidAlgebra R G) :=
  LinearMap.range (LinearMap.mulLeft R f)

def leftIdealAction
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) {S : Type w} [Group S]
    (phi : S →* G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (phi s)))
    (s : S) :
    leftIdeal R f →ₗ[R] leftIdeal R f :=
  (LinearMap.mulLeft R (MonoidAlgebra.of R G (phi s))).restrict (by
    rintro _ ⟨x, rfl⟩
    refine ⟨MonoidAlgebra.of R G (phi s) * x, ?_⟩
    change f * (MonoidAlgebra.of R G (phi s) * x) =
      MonoidAlgebra.of R G (phi s) * (f * x)
    rw [← mul_assoc, (hcomm s).eq, mul_assoc])

@[simp] theorem leftIdealAction_apply
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) {S : Type w} [Group S]
    (phi : S →* G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (phi s)))
    (s : S) (x : leftIdeal R f) :
    (leftIdealAction R f phi hcomm s x : MonoidAlgebra R G) =
      MonoidAlgebra.of R G (phi s) * (x : MonoidAlgebra R G) :=
  rfl

def leftIdealRepresentation
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) {S : Type w} [Group S]
    (phi : S →* G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (phi s))) :
    Representation R S (leftIdeal R f) where
  toFun := leftIdealAction R f phi hcomm
  map_one' := by
    ext x
    simp [leftIdealAction]
  map_mul' s t := by
    ext x
    simp [leftIdealAction, mul_assoc, map_mul]

/-! The left ideal cut out by an equivariant idempotent is already a split
summand of the restricted regular representation.  This elementary splitting
is useful when the ambient representation is the regular representation: no
relative-trace hypothesis is then needed to obtain projectivity. -/

/-- Inclusion of the equivariant left ideal into the restricted regular
representation. -/
def leftIdealInclusionIntertwiningMap
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) (S : Subgroup G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (S.subtype s))) :
    (leftIdealRepresentation R f S.subtype hcomm).IntertwiningMap
      (CentralIdempotentSupport.restrictedLeftRegularRepresentation R S) where
  toLinearMap := (leftIdeal R f).subtype
  isIntertwining' s := by
    apply LinearMap.ext
    intro x
    exact
      (CentralIdempotentSupport.leftRegular_apply_eq_mul
        (R := R) (G := G) (s : G) (x : MonoidAlgebra R G)).symm

/-- Left multiplication by `f`, with codomain restricted to its range, is
an equivariant projection whenever `f` commutes with the subgroup. -/
def leftIdealProjectionIntertwiningMap
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) (S : Subgroup G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (S.subtype s))) :
    (CentralIdempotentSupport.restrictedLeftRegularRepresentation R S).IntertwiningMap
      (leftIdealRepresentation R f S.subtype hcomm) where
  toLinearMap := (LinearMap.mulLeft R f).codRestrict (leftIdeal R f)
    (fun x ↦ ⟨x, rfl⟩)
  isIntertwining' s := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply]
    apply Subtype.ext
    change f * (show MonoidAlgebra R G from
        Representation.leftRegular R G (s : G) x) =
      MonoidAlgebra.of R G (s : G) * (f * x)
    rw [CentralIdempotentSupport.leftRegular_apply_eq_mul]
    have hscomm :
        f * MonoidAlgebra.of R G (s : G) =
          MonoidAlgebra.of R G (s : G) * f := by
      simpa using (hcomm s).eq
    calc
      f * (MonoidAlgebra.of R G (s : G) * x) =
          (f * MonoidAlgebra.of R G (s : G)) * x :=
        (mul_assoc _ _ _).symm
      _ = (MonoidAlgebra.of R G (s : G) * f) * x := by
        rw [hscomm]
      _ = MonoidAlgebra.of R G (s : G) * (f * x) :=
        mul_assoc _ _ _

/-- The inclusion above, regarded as a linear map over the subgroup
algebra. -/
abbrev leftIdealInclusionAsModule
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) (S : Subgroup G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (S.subtype s))) :
    (leftIdealRepresentation R f S.subtype hcomm).asModule
        →ₗ[MonoidAlgebra R S]
      (CentralIdempotentSupport.restrictedLeftRegularRepresentation R S).asModule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule _ _)
    (leftIdealInclusionIntertwiningMap R f S hcomm)

/-- The left-multiplication projection above, regarded as a linear map over
the subgroup algebra. -/
abbrev leftIdealProjectionAsModule
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) (S : Subgroup G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (S.subtype s))) :
    (CentralIdempotentSupport.restrictedLeftRegularRepresentation R S).asModule
        →ₗ[MonoidAlgebra R S]
      (leftIdealRepresentation R f S.subtype hcomm).asModule :=
  (Representation.IntertwiningMap.equivLinearMapAsModule _ _)
    (leftIdealProjectionIntertwiningMap R f S hcomm)

/-- For idempotent `f`, left multiplication splits the inclusion of its
equivariant left ideal over the subgroup algebra. -/
theorem leftIdealProjection_comp_inclusion
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) (hf : IsIdempotentElem f)
    (S : Subgroup G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (S.subtype s))) :
    (leftIdealProjectionAsModule R f S hcomm).comp
        (leftIdealInclusionAsModule R f S hcomm) = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x, hx⟩
  apply Subtype.ext
  rcases hx with ⟨y, hy⟩
  change f * x = x
  rw [← hy]
  change f * (f * y) = f * y
  rw [← mul_assoc, hf]

/-- An equivariant idempotent left ideal of the regular representation is
projective after restriction to the subgroup. -/
theorem projective_leftIdealRepresentation_asModule
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (f : MonoidAlgebra R G) (hf : IsIdempotentElem f)
    (S : Subgroup G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (S.subtype s))) :
    Module.Projective (MonoidAlgebra R S)
      (leftIdealRepresentation R f S.subtype hcomm).asModule := by
  letI : Module.Projective (MonoidAlgebra R S)
      (CentralIdempotentSupport.restrictedLeftRegularRepresentation R S).asModule :=
    CentralIdempotentSupport.projective_restrictedLeftRegular_asModule S
  exact Module.Projective.of_split
    (leftIdealInclusionAsModule R f S hcomm)
    (leftIdealProjectionAsModule R f S hcomm)
    (leftIdealProjection_comp_inclusion f hf S hcomm)

/-- For finite ambient `G`, the same equivariant left ideal is finite over
the subgroup algebra. -/
theorem finite_leftIdealRepresentation_asModule
    {R : Type u} {G : Type v} [CommRing R] [Group G] [Finite G]
    (f : MonoidAlgebra R G) (hf : IsIdempotentElem f)
    (S : Subgroup G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (S.subtype s))) :
    Module.Finite (MonoidAlgebra R S)
      (leftIdealRepresentation R f S.subtype hcomm).asModule := by
  letI : Module.Finite R
      (CentralIdempotentSupport.restrictedLeftRegularRepresentation R S).asModule :=
    inferInstance
  letI : Module.Finite (MonoidAlgebra R S)
      (CentralIdempotentSupport.restrictedLeftRegularRepresentation R S).asModule :=
    Module.Finite.of_restrictScalars_finite R (MonoidAlgebra R S)
      (CentralIdempotentSupport.restrictedLeftRegularRepresentation R S).asModule
  apply Module.Finite.of_surjective (leftIdealProjectionAsModule R f S hcomm)
  intro x
  refine ⟨leftIdealInclusionAsModule R f S hcomm x, ?_⟩
  have hx := LinearMap.congr_fun
    (leftIdealProjection_comp_inclusion f hf S hcomm) x
  simpa [LinearMap.comp_apply] using hx

def cornerLeftMul
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (f c : MonoidAlgebra R G)
    (hfc : f * c = c) (hcf : c * f = c) :
    leftIdeal R f →ₗ[R] leftIdeal R f :=
  (LinearMap.mulLeft R c).restrict (by
    rintro _ ⟨x, rfl⟩
    refine ⟨c * x, ?_⟩
    change f * (c * x) = c * (f * x)
    rw [← mul_assoc, hfc, ← mul_assoc, hcf])

@[simp] theorem cornerLeftMul_apply
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (f c : MonoidAlgebra R G)
    (hfc : f * c = c) (hcf : c * f = c)
    (x : leftIdeal R f) :
    (cornerLeftMul R f c hfc hcf x : MonoidAlgebra R G) =
      c * (x : MonoidAlgebra R G) :=
  rfl

def tracingEndomorphism
    (R : Type u) {G : Type v} [CommRing R] [Group G]
    (f c : MonoidAlgebra R G)
    (hfc : f * c = c) (hcf : c * f = c)
    {S : Type w} [Group S] (phi : S →* G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (phi s))) :
    (leftIdealRepresentation R f phi hcomm).asModule →ₗ[R]
      (leftIdealRepresentation R f phi hcomm).asModule :=
  let rho := leftIdealRepresentation R f phi hcomm
  rho.asModuleEquiv.symm.toLinearMap.comp
    ((cornerLeftMul R f c hfc hcf).comp rho.asModuleEquiv.toLinearMap)

@[simp] theorem tracingEndomorphism_apply
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (f c : MonoidAlgebra R G)
    (hfc : f * c = c) (hcf : c * f = c)
    {S : Type w} [Group S] (phi : S →* G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (phi s)))
    (x : (leftIdealRepresentation R f phi hcomm).asModule) :
    (((leftIdealRepresentation R f phi hcomm).asModuleEquiv
        (tracingEndomorphism R f c hfc hcf phi hcomm x) : leftIdeal R f) :
          MonoidAlgebra R G) =
      c * (((leftIdealRepresentation R f phi hcomm).asModuleEquiv x :
        leftIdeal R f) : MonoidAlgebra R G) :=
  rfl

theorem conjugate_tracingEndomorphism_apply_coe
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    (f c : MonoidAlgebra R G)
    (hfc : f * c = c) (hcf : c * f = c)
    {S : Type w} [Group S] (phi : S →* G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (phi s)))
    (s : S)
    (x : (leftIdealRepresentation R f phi hcomm).asModule) :
    ((((leftIdealRepresentation R f phi hcomm).asModuleEquiv
        ((tracingEndomorphism R f c hfc hcf phi hcomm).conjugate s x) :
          leftIdeal R f) : MonoidAlgebra R G)) =
      MonoidAlgebra.of R G ((phi s)⁻¹) * c *
        MonoidAlgebra.of R G (phi s) *
          (((leftIdealRepresentation R f phi hcomm).asModuleEquiv x :
            leftIdeal R f) : MonoidAlgebra R G) := by
  rw [LinearMap.conjugate_apply]
  simp only [Representation.single_smul, one_smul]
  change MonoidAlgebra.of R G (phi (s⁻¹)) *
      (c * (MonoidAlgebra.of R G (phi s) *
        (((leftIdealRepresentation R f phi hcomm).asModuleEquiv x :
          leftIdeal R f) : MonoidAlgebra R G))) = _
  rw [map_inv]
  simp only [mul_assoc]

theorem projective_of_exact_relativeTrace
    {R : Type u} {G : Type v} [CommRing R] [Group G]
    {S : Type w} [Group S] [Fintype S]
    (f c : MonoidAlgebra R G)
    (hf : IsIdempotentElem f)
    (hfc : f * c = c) (hcf : c * f = c)
    (phi : S →* G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (phi s)))
    (htrace : ∑ s : S,
        MonoidAlgebra.of R G (phi (s⁻¹)) * c *
          MonoidAlgebra.of R G (phi s) = f)
    [Module.Free R (leftIdeal R f)] :
    Module.Projective (MonoidAlgebra R S)
      (leftIdealRepresentation R f phi hcomm).asModule := by
  let rho := leftIdealRepresentation R f phi hcomm
  letI : Module.Free R rho.asModule :=
    Module.Free.of_equiv rho.asModuleEquiv.symm
  let a : rho.asModule →ₗ[R] rho.asModule :=
    tracingEndomorphism R f c hfc hcf phi hcomm
  change Module.Projective (MonoidAlgebra R S) rho.asModule
  refine HigmanScratch.projective_of_relative_trace_id
    (R := R) (P := S) (M := rho.asModule) a ?_
  apply LinearMap.ext
  intro x
  apply rho.asModuleEquiv.injective
  apply Subtype.ext
  let X : MonoidAlgebra R G :=
    (rho.asModuleEquiv x : leftIdeal R f)
  have hX : f * X = X := by
    rcases (rho.asModuleEquiv x).property with ⟨y, hy⟩
    change f * y = X at hy
    calc
      f * X = f * (f * y) := by rw [hy]
      _ = (f * f) * y := (mul_assoc _ _ _).symm
      _ = f * y := by rw [hf]
      _ = X := hy
  simp only [LinearMap.sum_apply, LinearMap.id_apply, map_sum]
  have hcoe :
      (((∑ s : S, rho.asModuleEquiv (a.conjugate s x)) : leftIdeal R f) :
        MonoidAlgebra R G) =
      ∑ s : S, ((rho.asModuleEquiv (a.conjugate s x) : leftIdeal R f) :
        MonoidAlgebra R G) := by
    simp
  rw [hcoe]
  change (∑ s : S,
      (((rho.asModuleEquiv (a.conjugate s x) : leftIdeal R f) :
        MonoidAlgebra R G))) = X
  simp_rw [show ∀ s : S,
      (((rho.asModuleEquiv (a.conjugate s x) : leftIdeal R f) :
        MonoidAlgebra R G)) =
        MonoidAlgebra.of R G (phi (s⁻¹)) * c *
          MonoidAlgebra.of R G (phi s) * X by
      intro s
      simpa [a, rho] using
        conjugate_tracingEndomorphism_apply_coe
          f c hfc hcf phi hcomm s x]
  rw [← Finset.sum_mul, htrace, hX]

theorem projective_of_exact_relativeTrace_of_local
    {R : Type u} {G : Type v} [CommRing R] [IsLocalRing R]
    [Group G] [Finite G] {S : Type w} [Group S] [Fintype S]
    (f c : MonoidAlgebra R G)
    (hf : IsIdempotentElem f)
    (hcorner : f * c * f = c)
    (phi : S →* G)
    (hcomm : ∀ s : S,
      Commute f (MonoidAlgebra.of R G (phi s)))
    (htrace : ∑ s : S,
        MonoidAlgebra.of R G (phi (s⁻¹)) * c *
          MonoidAlgebra.of R G (phi s) = f) :
    Module.Projective (MonoidAlgebra R S)
      (leftIdealRepresentation R f phi hcomm).asModule := by
  let p : MonoidAlgebra R G →ₗ[R] MonoidAlgebra R G :=
    LinearMap.mulLeft R f
  have hp : IsIdempotentElem p := by
    change (LinearMap.mulLeft R f).comp
        (LinearMap.mulLeft R f) = LinearMap.mulLeft R f
    rw [← LinearMap.mulLeft_mul, hf]
  letI : Module.Projective R (MonoidAlgebra R G) :=
    Module.Projective.of_free
  letI : Module.Finite R (MonoidAlgebra R G) := inferInstance
  letI : Module.Free R (leftIdeal R f) := by
    change Module.Free R (LinearMap.range p)
    exact CentralIdempotentSupport.free_range_of_isIdempotentElem_of_isLocalRing
      p hp
  have hfc : f * c = c := by
    calc
      f * c = f * (f * c * f) := by rw [hcorner]
      _ = (f * f) * c * f := by ac_rfl
      _ = f * c * f := by rw [hf]
      _ = c := hcorner
  have hcf : c * f = c := by
    calc
      c * f = (f * c * f) * f := by rw [hcorner]
      _ = f * c * (f * f) := by ac_rfl
      _ = f * c * f := by rw [hf]
      _ = c := hcorner
  exact projective_of_exact_relativeTrace
    f c hf hfc hcf phi hcomm htrace

theorem projective_zpowers_leftIdeal_of_fixed_coeff_mem_maximalIdeal
    {R : Type u} {G : Type v} [CommRing R] [IsLocalRing R]
    [Group G] [Finite G]
    (z : G) (hzne : z ≠ 1) (hz : z * z = 1)
    (f : MonoidAlgebra R G) (hf : IsIdempotentElem f)
    (hfinv : BrauerKernelRelativeTrace.conjugation R z f = f)
    (hfixed : ∀ x : G, z⁻¹ * x * z = x →
      f x ∈ IsLocalRing.maximalIdeal R) :
    Module.Projective (MonoidAlgebra R (Subgroup.zpowers z))
      (leftIdealRepresentation R f (Subgroup.zpowers z).subtype
        (commute_zpowers_of_conjugation_fixed z hzne hz f hfinv)).asModule := by
  classical
  obtain ⟨c, hcorner, htrace⟩ :=
    ExactRelativeTrace.exists_exact_relativeTrace_of_fixed_coeff_mem_maximalIdeal
      z hz f hf hfinv hfixed
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzord : orderOf z = 2 := by
    apply orderOf_eq_prime (p := 2)
    · rw [pow_two, hz]
    · exact hzne
  let S : Subgroup G := Subgroup.zpowers z
  have hScard : Nat.card S = 2 := by
    dsimp [S]
    rw [Nat.card_zpowers, hzord]
  let zS : S := ⟨z, Subgroup.mem_zpowers z⟩
  have hzSne : zS ≠ 1 := by
    intro h
    apply hzne
    exact congrArg Subtype.val h
  obtain ⟨q, hq, hunique⟩ := (Nat.card_eq_two_iff' (1 : S)).mp hScard
  have hall (s : S) : s = 1 ∨ s = zS := by
    by_cases hs : s = 1
    · exact Or.inl hs
    · exact Or.inr ((hunique s hs).trans (hunique zS hzSne).symm)
  have huniv : (Finset.univ : Finset S) = {1, zS} := by
    ext s
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    exact hall s
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  let hcomm := commute_zpowers_of_conjugation_fixed z hzne hz f hfinv
  have hsum :
      ∑ s : S,
          MonoidAlgebra.of R G (S.subtype (s⁻¹)) * c *
            MonoidAlgebra.of R G (S.subtype s) = f := by
    rw [huniv, Finset.sum_pair hzSne.symm]
    have htrace' := htrace
    rw [conjugation_eq_group_elements_mul, hzinv] at htrace'
    simpa [S, zS, hzinv, ← MonoidAlgebra.one_def] using htrace'.symm
  exact projective_of_exact_relativeTrace_of_local
    f c hf hcorner S.subtype hcomm hsum

end LeftIdealHigman
end Submission.ZStar
