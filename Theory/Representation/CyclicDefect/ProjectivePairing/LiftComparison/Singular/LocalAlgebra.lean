module

public import Theory.Representation.CyclicDefect.ProjectivePairing.LiftComparison.Singular.Inputs
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.GroupTheory.PGroup

/-!
# Local algebras of finite abelian p-groups

Let `R` be a commutative local ring whose maximal ideal contains the prime `p`.
For a finite abelian `p`-group `P`, the group algebra `R[P]` is local, and its
finitely generated projective modules are free. In particular this applies to
the integral lift restricted to a `p`-subgroup of a cyclic subgroup.

The group algebra is finite, hence integral, over `R`. Every maximal ideal
therefore contracts to the maximal ideal of `R`. Its residue field has
characteristic `p`, so injectivity of Frobenius sends every group element to
one. Every maximal ideal is consequently the inverse image of the coefficient
maximal ideal under augmentation. Finite projective freeness then follows
from the local-ring theorem for finite flat modules.

This provides the locality and freeness inputs to the cyclic proof of the
singular-vanishing clause of Feit, *The Representation Theory of Finite Groups*,
IV.2.5 (printed p. 144). Compare III.2.9 for the field case and I.10.2 for the
unique-maximal-ideal criterion. The remaining cyclic trace argument and final
assembly of IV.2.5 belong to the consumers of this module.
-/

public section
noncomputable section

namespace Representation.CyclicDefect.ProjectivePairing.Singular

/-- The algebra of a finite abelian `p`-group over a commutative local ring is
local when `p` belongs to the coefficient ring's maximal ideal. -/
theorem isLocalRing_monoidAlgebra {R P : Type*} [CommRing R] [IsLocalRing R]
    [CommGroup P] [Finite P] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) ∈ IsLocalRing.maximalIdeal R) (hP : IsPGroup p P) :
    IsLocalRing (MonoidAlgebra R P) := by
  let ε : MonoidAlgebra R P →+* R := MonoidAlgebra.liftNCRingHom (RingHom.id R) (1 : P →* R)
    (fun _ _ => Commute.one_right _)
  have hε (g : P) (r : R) : ε (MonoidAlgebra.single g r) = r := by
    simp only [ε, MonoidAlgebra.liftNCRingHom_single, RingHom.id_apply,
      MonoidHom.one_apply, mul_one]
  have hsurj : Function.Surjective ε := fun r => ⟨MonoidAlgebra.single 1 r, hε 1 r⟩
  let : Module.Finite R (MonoidAlgebra R P) := Module.Finite.of_basis (MonoidAlgebra.basis P R)
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨(IsLocalRing.maximalIdeal R).comap ε,
    Ideal.comap_isMaximal_of_surjective _ hsurj, ?_⟩
  intro I hI
  let : I.IsMaximal := hI
  have hcontract : I.comap (algebraMap R (MonoidAlgebra R P)) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal I)
  have hpI : (p : MonoidAlgebra R P) ∈ I := by
    have h : (p : R) ∈ I.comap (algebraMap R (MonoidAlgebra R P)) := hcontract.symm ▸ hp
    simpa only [Ideal.mem_comap, map_natCast] using h
  let : CharP (MonoidAlgebra R P ⧸ I) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
      rw [← map_natCast (Ideal.Quotient.mk I)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hpI)
  have hsingle (g : P) : Ideal.Quotient.mk I (MonoidAlgebra.single g (1 : R)) = 1 := by
    obtain ⟨n, hn⟩ := hP.exists_pow_pow_eq_one g
    apply iterateFrobenius_inj (MonoidAlgebra R P ⧸ I) p n
    change Ideal.Quotient.mk I (MonoidAlgebra.single g (1 : R)) ^ (p ^ n) = 1 ^ (p ^ n)
    rw [← map_pow, MonoidAlgebra.single_pow, hn]
    simp only [one_pow, ← MonoidAlgebra.one_def, map_one]
  have hmap : Ideal.Quotient.mk I =
      ((Ideal.Quotient.mk I).comp (algebraMap R (MonoidAlgebra R P))).comp ε := by
    apply MonoidAlgebra.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, hε]
      rfl
    · intro g
      simp [hε, hsingle]
  ext x
  change x ∈ I ↔ ε x ∈ IsLocalRing.maximalIdeal R
  rw [← hcontract]
  change x ∈ I ↔ algebraMap R (MonoidAlgebra R P) (ε x) ∈ I
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.eq_zero_iff_mem]
  exact Iff.of_eq (congrArg (fun y => y = 0) (RingHom.congr_fun hmap x))

/-- Finitely generated projective modules over this local group algebra are free. -/
theorem free_of_projective_monoidAlgebra {R P M : Type*} [CommRing R] [IsLocalRing R]
    [CommGroup P] [Finite P] (p : ℕ) [Fact p.Prime]
    (hp : (p : R) ∈ IsLocalRing.maximalIdeal R) (hP : IsPGroup p P)
    [AddCommGroup M] [Module (MonoidAlgebra R P) M]
    [Module.Finite (MonoidAlgebra R P) M] [Module.Projective (MonoidAlgebra R P) M] :
    Module.Free (MonoidAlgebra R P) M := by
  let := isLocalRing_monoidAlgebra p hp hP
  exact Module.free_of_flat_of_isLocalRing

end Representation.CyclicDefect.ProjectivePairing.Singular

namespace Representation.CyclicDefect.ProjectivePairing.IntegralLift

attribute [local instance] IntegralLift.coeffRing IntegralLift.coeffLocal
open scoped IsMulCommutative

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  {m : ℕ} {L : CyclicRootLift K m} {Q : Representation K G V} (A : IntegralLift L Q)

/-- Locality for the literal `p`-subgroup algebra used by an integral cyclic lift.
The residue-kernel condition supplies the maximal-ideal hypothesis. -/
theorem isLocalRing_pSubgroupAlgebra [Finite G] (p : ℕ) [Fact p.Prime] [CharP K p]
    (g : G) (P : Subgroup (Subgroup.zpowers g)) (hP : IsPGroup p P) :
    IsLocalRing (MonoidAlgebra A.Coeff P) :=
  Singular.isLocalRing_monoidAlgebra p (A.prime_mem_maximalIdeal p) hP

/-- The integral lift restricted to a `p`-subgroup of its cyclic action is free
over that subgroup algebra. Projectivity is supplied by subgroup restriction;
finite generation follows from the given finite coefficient module. -/
theorem cyclicRep_free_pSubgroup [Finite G] (p : ℕ) [Fact p.Prime] [CharP K p]
    (g : G) (P : Subgroup (Subgroup.zpowers g)) (hP : IsPGroup p P) :
    Module.Free (MonoidAlgebra A.Coeff P)
      (Representation.asModule ((A.cyclicRep g).comp P.subtype)) := by
  let : Fintype (Subgroup.zpowers g) := Fintype.ofFinite _
  let : Module.Projective (MonoidAlgebra A.Coeff (Subgroup.zpowers g))
      (A.cyclicRep g).asModule := A.cyclicRep_projective g
  let : Module.Projective (MonoidAlgebra A.Coeff P)
      (Representation.asModule ((A.cyclicRep g).comp P.subtype)) :=
    Singular.projective_subgroup (A.cyclicRep g) P
  let : Module.Finite (MonoidAlgebra A.Coeff P)
      (Representation.asModule ((A.cyclicRep g).comp P.subtype)) :=
    Module.Finite.of_restrictScalars_finite A.Coeff _ _
  exact Singular.free_of_projective_monoidAlgebra p (A.prime_mem_maximalIdeal p) hP

end Representation.CyclicDefect.ProjectivePairing.IntegralLift
