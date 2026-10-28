module

public import Theory.Character.ModularBlock.LeftIdealRestriction
public import Theory.Character.ModularBlock.IdempotentTrace
public import Theory.Representation.HigmanRelativeTrace

/-!
# Left Ideal Relative Trace

A tracing element in an idempotent corner acts on the image of left
multiplication. If the sum of its subgroup conjugates is the idempotent,
its induced endomorphism has relative trace equal to the identity. Higman's
criterion then makes the image representation projective when it is free
over the coefficient ring. For a finite ambient group over a local ring,
that scalar freeness follows from the idempotent splitting.

The corner multiplication and tracing endomorphism are exposed for their
coefficient-action interface in the later projective-range argument.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/LeftIdealHigman.lean` (revision `c3503435`).
-/

@[expose] public section

noncomputable section

namespace ModularBlock.LeftIdealHigman

universe u v w

attribute [local instance] Fintype.ofFinite

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
  let : Module.Free R rho.asModule :=
    Module.Free.of_equiv rho.asModuleEquiv.symm
  let a : rho.asModule →ₗ[R] rho.asModule :=
    tracingEndomorphism R f c hfc hcf phi hcomm
  change Module.Projective (MonoidAlgebra R S) rho.asModule
  refine HigmanRelativeTrace.projective_of_relative_trace_id
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
  let : Module.Projective R (MonoidAlgebra R G) :=
    Module.Projective.of_free
  let : Module.Finite R (MonoidAlgebra R G) := inferInstance
  let : Module.Free R (leftIdeal R f) := by
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

end ModularBlock.LeftIdealHigman

