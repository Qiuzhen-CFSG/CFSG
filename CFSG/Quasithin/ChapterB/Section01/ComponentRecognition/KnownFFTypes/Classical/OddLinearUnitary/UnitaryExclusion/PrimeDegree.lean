module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.SourceReduction
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.PrimeDegree.Inputs
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.PrimeDegree.CenterCoprime
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion.PrimeDegree.RootGeometry
public import Theory.Representation.BinaryCoprimeDegree.RationalExtraspecial

/-!
# The odd PSU₃ binary degree minimum

The rational extraspecial subgroup argument gives p(p−1) on the original
binary module. It applies to the actual component after lifting the concrete
projective root subgroup through the literal center quotient. The concrete
root configuration and defining-prime coprimality of the covering center
are proved in the imported modules and assembled in `primeDegreeBound`.

The source SQTK, quasisimple and irreducible hypotheses remain intact,
with the original binary field and every source central cover retained.
The source consumer discharges the degree premise of SourceReduction;
conjugate generation, outer displacement at five and the cubic-ratio bound
remain separate premises. The earlier conditional APIs are preserved.

Sources: Aschbacher–Smith K.2, printed p.453; Guralnick–Malle,
Classification of 2F-modules I, Proposition 4.3, manuscript p.10, and its
Seitz–Zalesskii degree estimate. The covering-center result follows from
the defining-prime kernel exclusion for arbitrary perfect central covers.
-/

public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
universe u v

variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [IsQuasisimple L]

omit [IsQuasisimple L] in
/-- Apply the rational extraspecial bound on the original binary space, after
lifting the concrete projective root configuration through the literal center
quotient. The field and Hermitian-form witnesses are retained. -/
theorem source_prime_degree_of_root_geometry
    (hgeometry : PrimeDegreeRootGeometry) {p : ℕ}
    (h : SourceHypotheses ρ L p) (hp : 3 < p)
    (hcop : Nat.Coprime p (Nat.card (center L))) :
    p * (p - 1) ≤ Module.finrank (ZMod 2) V := by
  let : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h.quotient
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = center L := by
    ext x
    change e ((QuotientGroup.mk' (center L)) x) = 1 ↔ x ∈ center L
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hlocal := (hgeometry F J h.prime hp hcard hconj).of_central_coprime
    f hf (by rw [hker]) (by rwa [hker])
  exact BinaryCoprimeDegree.finrank_ge_of_rational_extraspecial
    (by omega : p ≠ 2) (ρ.comp L.subtype)
    (h.faithful.comp L.subtype_injective) hlocal

/-- Conditional assembly of the exact source degree contract from concrete
root geometry and prime-to-p central kernel order. -/
theorem primeDegreeBound_of_local_inputs
    (hgeometry : PrimeDegreeRootGeometry) (hcenter : PrimeDegreeCenterCoprime.{u, v}) :
    PrimeDegreeBound.{u, v} := by
  intro G V _ _ _ _ _ ρ L _ p h hp
  exact source_prime_degree_of_root_geometry ρ L hgeometry h hp (hcenter ρ L h hp)

/-- The source odd-prime PSU₃ degree minimum on the original binary module,
with the root geometry and covering-center coprimality fully discharged. -/
theorem primeDegreeBound : PrimeDegreeBound.{u, v} :=
  primeDegreeBound_of_local_inputs primeDegreeRootGeometry primeDegreeCenterCoprime

/-- The existing K.2 consumer with its degree premise discharged by the local
argument, retaining the local inputs as explicit conditional parameters. -/
theorem source_parameter_eq_three_of_prime_local_inputs
    (hgeometry : PrimeDegreeRootGeometry) (hcenter : PrimeDegreeCenterCoprime.{u, v})
    (hconjugates : SourceConjugateBounds.{u, v})
    (houter : SourceFiveOuterDisplacement.{u, v})
    {p : ℕ} (h : SourceHypotheses ρ L p)
    (hq : Representation.BinaryOffender.cubicRatio ρ ≤ 2) : p = 3 :=
  source_parameter_eq_three_of_inputs ρ L
    (primeDegreeBound_of_local_inputs hgeometry hcenter) hconjugates houter h hq

/-- Apply the proved degree minimum to the actual K.2 source reduction.
The separate conjugate-generation and five-parameter outer-displacement
inputs remain with their source assembly owner. -/
theorem source_parameter_eq_three_of_prime_degree
    (hconjugates : SourceConjugateBounds.{u, v})
    (houter : SourceFiveOuterDisplacement.{u, v})
    {p : ℕ} (h : SourceHypotheses ρ L p)
    (hq : Representation.BinaryOffender.cubicRatio ρ ≤ 2) : p = 3 :=
  source_parameter_eq_three_of_prime_local_inputs ρ L
    primeDegreeRootGeometry primeDegreeCenterCoprime hconjugates houter h hq

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
