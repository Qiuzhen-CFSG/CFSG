module

public import Theory.Representation.CyclicDefect.ProjectivePairing.IntegralLifting.Idempotents
public import Theory.Representation.CyclicDefect.ProjectivePairing.IntegralLifting.Transport
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.AlgebraTower

/-!
# Realizing projective residue lifts

A finite projective representation over `k[G]` splits off a finite free
`k[G]`-module. Its projection is a matrix acting on row vectors on the right;
this convention makes the summand a left group-algebra module. Lift that
idempotent matrix and take its range. This range is projective over `R[G]`
and finite projective, hence free, over the local coefficient ring `R`.

The reduction equivalence is constructed from the original projection and
entrywise coefficient reduction. Surjectivity follows by lifting the original
inclusion. Injectivity follows because the lifted projection preserves the
kernel of coefficient reduction. Thus the construction retains the actual
action and reduction maps, not only a dimension comparison.

`CompleteCoefficientRing.residueProjectiveLift` discharges the residue-module
input of `assemble`; `assembleProjective` is its direct consumer.

Source: Feit, *The Representation Theory of Finite Groups*, I.13.7(i), p.44,
using the idempotent lifting of I.12.3--4 and coefficient setting of I.17,
pp.63--64. The matrix argument treats all finite projectives simultaneously.
-/

public section
noncomputable section
open scoped BigOperators
open Module
namespace Representation.CyclicDefect.ProjectivePairing.IntegralLifting
variable {R k G : Type*} [CommRing R] [Field k] [Group G] [Fintype G]

private def freeReduction (f : R →+* k) (s : ℕ) :
    (Fin s → MonoidAlgebra R G) →ₛₗ[f] (Fin s → MonoidAlgebra k G) where
  toFun x i := MonoidAlgebra.mapRingHom G f (x i)
  map_add' x y := by ext i g; simp
  map_smul' r x := by ext i g; simp

omit [Fintype G] in
private lemma freeReduction_surjective (f : R →+* k) (hf : Function.Surjective f) (s : ℕ) :
    Function.Surjective (freeReduction (G := G) f s) := by
  intro y
  have h := MonoidAlgebra.map_surjective (M := G) f.toAddMonoidHom hf
  choose x hx using fun i => h (y i)
  exact ⟨x, funext hx⟩

omit [Fintype G] in
private lemma freeReduction_vecMul (f : R →+* k) (s : ℕ)
    (e : Matrix (Fin s) (Fin s) (MonoidAlgebra R G)) (x : Fin s → MonoidAlgebra R G) :
    freeReduction f s (e.toLinearMapRight' x) =
      ((MonoidAlgebra.mapRingHom G f).mapMatrix e).toLinearMapRight' (freeReduction f s x) := by
  funext i
  exact (MonoidAlgebra.mapRingHom G f).map_vecMul e x i

private lemma freeReduction_kernel (f : R →+* k) {s d : ℕ}
    (h : (Fin s → MonoidAlgebra R G) →ₗ[R] (Fin d → R))
    (x : Fin s → MonoidAlgebra R G) (hx : freeReduction f s x = 0) :
    f ∘ h x = 0 := by
  classical
  let b := (MonoidAlgebra.basis G R).smulTower (Pi.basisFun (MonoidAlgebra R G) (Fin s))
  have hcoeff (j : G × Fin s) : f (b.repr x j) = 0 := by
    have hh := congrArg (fun y => (y j.2).coeff j.1) hx
    change f ((x j.2).coeff j.1) = 0
    simpa [freeReduction] using hh
  rw [← b.sum_repr x, map_sum]
  ext i
  simp only [Function.comp_apply, Finset.sum_apply, map_smul, Pi.smul_apply,
    smul_eq_mul, map_sum, map_mul, hcoeff, zero_mul, Finset.sum_const_zero, Pi.zero_apply]

private def residueLinear {d n : ℕ} (f : R →+* k)
    (u : (Fin d → R) →ₛₗ[f] (Fin n → k)) : (Fin d → k) →ₗ[k] (Fin n → k) :=
  (Pi.basisFun k (Fin d)).constr k (fun i => u (Pi.single i 1))

private lemma residueLinear_apply {d n : ℕ} (f : R →+* k)
    (u : (Fin d → R) →ₛₗ[f] (Fin n → k)) (x : Fin d → R) :
    residueLinear f u (f ∘ x) = u x := by
  classical
  conv_rhs => rw [← (Pi.basisFun R (Fin d)).sum_repr x, map_sum]
  simp [residueLinear, map_smulₛₗ]

omit [Fintype G] in
private lemma mapCoefficients_apply_map {d : ℕ} (f : R →+* k)
    (ρ : Representation R G (Fin d → R)) (g : G) (x : Fin d → R) :
    mapCoefficients f ρ g (f ∘ x) = f ∘ (ρ g x) := by
  ext i
  change (Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map f) (f ∘ x)) i = _
  rw [Matrix.toLin'_apply, ← RingHom.map_mulVec, ← Matrix.toLin'_apply,
    Matrix.toLin'_toMatrix']
  rfl

section Coordinates
variable {P : Type*} [AddCommGroup P] [Module R P] [Module (MonoidAlgebra R G) P]
  [IsScalarTower R (MonoidAlgebra R G) P] {d : ℕ}
private def moduleCoordinates (b : P ≃ₗ[R] (Fin d → R)) :
    Representation R G (Fin d → R) :=
  b.conjRingEquiv.toMonoidHom.comp (Representation.ofModule' P)
omit [Fintype G] in
private lemma moduleCoordinates_apply (b : P ≃ₗ[R] (Fin d → R))
    (g : G) (x : Fin d → R) :
    moduleCoordinates b g x = b (MonoidAlgebra.of R G g • b.symm x) := by
  rfl
private def moduleCoordinatesEquiv (b : P ≃ₗ[R] (Fin d → R)) :
    P ≃ₗ[MonoidAlgebra R G] (moduleCoordinates (G := G) b).asModule where
  toAddEquiv := b.toAddEquiv.trans (moduleCoordinates b).asModuleEquiv.symm.toAddEquiv
  map_smul' a x := by
    change (moduleCoordinates b).asModuleEquiv.symm (b (a • x)) =
      a • (moduleCoordinates b).asModuleEquiv.symm (b x)
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a c ha hc => simpa only [add_smul, map_add] using congrArg₂ (· + ·) ha hc
    | single g r =>
      have hr : MonoidAlgebra.single g r = r • MonoidAlgebra.of R G g := by
        simp [MonoidAlgebra.of_apply]
      rw [hr, smul_assoc, smul_assoc, b.map_smul, map_smul]
      congr 1
      rw [← (moduleCoordinates b).asModuleEquiv_symm_map_rho,
        moduleCoordinates_apply, b.symm_apply_apply]
end Coordinates

omit [Fintype G] in
private lemma freeReduction_smul (f : R →+* k) (s : ℕ)
    (a : MonoidAlgebra R G) (x : Fin s → MonoidAlgebra R G) :
    freeReduction f s (a • x) = MonoidAlgebra.mapRingHom G f a • freeReduction f s x := by
  funext i
  exact map_mul (MonoidAlgebra.mapRingHom G f) a (x i)

/-- A projective residue representation lifts whenever group-algebra matrix
idempotents lift and the coefficient ring is local. -/
theorem nonempty_residueProjectiveLift_of_matrixIdempotentsLift [IsLocalRing R]
    (f : R →+* k) (hf : Function.Surjective f) (hlift : MatrixIdempotentsLift f G)
    {n : ℕ} (Q : Representation k G (Fin n → k))
    [Module.Projective (MonoidAlgebra k G) Q.asModule] :
    Nonempty (ResidueProjectiveLift f Q) := by
  classical
  let A := MonoidAlgebra R G
  let B := MonoidAlgebra k G
  let : Module.Finite B Q.asModule := .of_restrictScalars_finite k B Q.asModule
  obtain ⟨s, q, i, _hq, _hi, hqi⟩ := Module.Finite.exists_comp_eq_id_of_projective B Q.asModule
  let e := (i.comp q).toMatrixRight'
  have he : IsIdempotentElem e := by
    change e * e = e
    rw [← LinearMap.toMatrixRight'_comp]
    apply congrArg LinearMap.toMatrixRight'
    apply LinearMap.ext
    intro x
    change i (q (i (q x))) = i (q x)
    rw [show q (i (q x)) = q x from LinearMap.congr_fun hqi (q x)]
  obtain ⟨E, hE, hred⟩ := (matrixIdempotentsLift_iff f).mp hlift s e he
  let p : (Fin s → A) →ₗ[A] (Fin s → A) := E.toLinearMapRight'
  have hp : IsIdempotentElem p := by
    change p.comp p = p
    change E.toLinearMapRight'.comp E.toLinearMapRight' = E.toLinearMapRight'
    rw [← Matrix.toLinearMapRight'_mul, hE.eq]
  let P := p.range
  let inc : P →ₗ[A] (Fin s → A) := p.range.subtype
  let pr : (Fin s → A) →ₗ[A] P := p.rangeRestrict
  have hpr : pr.comp inc = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (LinearMap.IsIdempotentElem.isProj_range p hp).map_id x x.2
  let : Module.Projective A P := Module.Projective.of_split inc pr hpr
  let : Module.Projective R P := Module.Projective.of_split
    (inc.restrictScalars R) (pr.restrictScalars R)
    (by apply LinearMap.ext; intro x; exact LinearMap.congr_fun hpr x)
  let : Module.Finite R P := Module.Finite.of_surjective
    (pr.restrictScalars R) p.surjective_rangeRestrict
  let : Module.Free R P := Module.free_of_flat_of_isLocalRing
  let b := (Module.finBasis R P).equivFun
  let d := Module.finrank R P
  let ρ : Representation R G (Fin d → R) := moduleCoordinates b
  have hρ : Module.Projective A ρ.asModule :=
    Module.Projective.of_equiv (moduleCoordinatesEquiv b)
  let c := freeReduction (G := G) f s
  have hcp (x : Fin s → A) : c (p x) = i (q (c x)) := by
    have h := freeReduction_vecMul f s E x
    rw [hred] at h
    simpa only [e, LinearEquiv.symm_apply_apply, LinearMap.comp_apply] using h
  let u₀ : (Fin d → R) →ₛₗ[f] (Fin n → k) :=
    (Q.asModuleEquiv.toLinearMap.comp (q.restrictScalars k)).comp
      (c.comp ((inc.restrictScalars R).comp b.symm.toLinearMap))
  let u := residueLinear f u₀
  have hu (x : Fin d → R) : u (f ∘ x) = Q.asModuleEquiv (q (c (inc (b.symm x)))) :=
    residueLinear_apply f u₀ x
  have hu_inj : Function.Injective u := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    choose z hz using fun j => hf (x j)
    have hz' : f ∘ z = x := funext hz
    rw [← hz', hu] at hx
    have hq : q (c (inc (b.symm z))) = 0 := Q.asModuleEquiv.injective (by simpa using hx)
    have hc : c (inc (b.symm z)) = 0 := by
      have h := hcp (inc (b.symm z))
      have hpz : p (inc (b.symm z)) = inc (b.symm z) :=
        (LinearMap.IsIdempotentElem.isProj_range p hp).map_id _ (b.symm z).2
      rw [hpz, hq, map_zero] at h
      exact h
    have hz0 := freeReduction_kernel f (b.toLinearMap.comp (pr.restrictScalars R))
      (inc (b.symm z)) hc
    have hpz : pr (inc (b.symm z)) = b.symm z := LinearMap.congr_fun hpr _
    change f ∘ b (pr (inc (b.symm z))) = 0 at hz0
    simpa only [hpz, b.apply_symm_apply, hz'] using hz0
  have hu_surj : Function.Surjective u := by
    intro y
    obtain ⟨x, hx⟩ := freeReduction_surjective f hf s (i (Q.asModuleEquiv.symm y))
    refine ⟨f ∘ b (pr x), ?_⟩
    rw [hu, b.symm_apply_apply]
    change Q.asModuleEquiv (q (c (p x))) = y
    rw [hcp, hx]
    have hqi' (v : Q.asModule) : q (i v) = v := LinearMap.congr_fun hqi v
    rw [hqi', hqi', Q.asModuleEquiv.apply_symm_apply]
  refine ⟨⟨d, ρ, hρ, .mk (LinearEquiv.ofBijective u ⟨hu_inj, hu_surj⟩) ?_⟩⟩
  intro g
  apply LinearMap.ext
  intro x
  change u (mapCoefficients f ρ g x) = Q g (u x)
  choose z hz using fun j => hf (x j)
  have hz' : f ∘ z = x := funext hz
  rw [← hz', mapCoefficients_apply_map, hu, hu]
  change Q.asModuleEquiv (q (c (inc (b.symm (moduleCoordinates b g z))))) = _
  rw [moduleCoordinates_apply, b.symm_apply_apply, inc.map_smul]
  rw [show c (MonoidAlgebra.of R G g • inc (b.symm z)) =
      MonoidAlgebra.of k G g • c (inc (b.symm z)) by
    rw [freeReduction_smul]; simp [MonoidAlgebra.of_apply]; rfl]
  rw [q.map_smul, Q.asModuleEquiv_map_smul, Q.asAlgebraHom_of]

/-- The complete coefficient ring lifts a finite projective residue representation,
including projectivity over its group algebra and the actual reduction equivalence. -/
def CompleteCoefficientRing.residueProjectiveLift {m n : ℕ} {L : CyclicRootLift k m}
    (C : CompleteCoefficientRing L) (Q : Representation k G (Fin n → k))
    [Module.Projective (MonoidAlgebra k G) Q.asModule] :
    ResidueProjectiveLift C.residue Q :=
  Classical.choice (nonempty_residueProjectiveLift_of_matrixIdempotentsLift
    C.residue C.residue_surjective C.matrixIdempotentsLift Q)

/-- Apply the lifted summand directly to integral-lift assembly. The complete
coefficient ring is the only remaining lifting input; no residue-lift premise remains. -/
def assembleProjective {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {m n : ℕ} {L : CyclicRootLift K m} {L₀ : CyclicRootLift k m}
    (j : k →+* K) (hz : j L₀.modularRoot = L.modularRoot)
    (hc : L₀.complexRoot = L.complexRoot) (C : CompleteCoefficientRing L₀)
    {τ : Representation k G (Fin n → k)} {Q : Representation K G V}
    [Module.Projective (MonoidAlgebra k G) τ.asModule]
    (a : (mapCoefficients j τ).Equiv Q) : IntegralLift L Q :=
  assemble j hz hc C a (C.residueProjectiveLift τ)

end Representation.CyclicDefect.ProjectivePairing.IntegralLifting
