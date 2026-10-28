module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerActors
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.Maximality
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.WreathedNormalizer

/-!
# Geometry after containment of an inner PSU₃ involution centralizer

`InnerGeometry.false_of_centralizer_le` completes the geometry conditional on
containment of the centralizer of a Sylow-central socle involution. Intrinsic
maximality identifies the proper obstruction overgroup with that centralizer.
Consequently every solvable Sylow overgroup centralizes the involution, as does
every odd-prime commutator normalized by the Sylow centralizer of an actual inner
four-group from the original family. The latter containment uses literal local
E-members and their quotient ranks.

For `p ≡ 3 (mod 4)`, the characteristic wreathed-base normalizer is a solvable
Sylow overgroup moving the involution. For `p ≡ 1 (mod 4)`, the normalized odd
torus has a commutator moving it. The proved matrix constructions discharge both
branches, including `p = 3` and arbitrary ambient two-extensions. The original
family is retained, including its possible outer actors.

Construction of the central involution and containment of its full centralizer
belong to the inner-family assembly and its independent centralizer-structure
input. These remain the explicit premises of this conditional theorem.

Source: Aschbacher--Smith, E.1.14(7), printed p.214, A.2.3(2), p.33, and
A.3.21, p.55; Aschbacher, *GF(2)-representations of finite groups* (1982),
Lemma 4.11.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry

variable {G : Type*} [Group G] [Finite G]

/-- Conditional inner-family geometry for E.1.14(7): once the obstruction
contains the full centralizer of the specified Sylow-central socle involution,
the actual unitary model supplies a contradiction in each odd-prime congruence
case. The centralizer-containment premise is discharged by the separate
centralizer-structure argument in the source theorem's inner-family assembly. -/
theorem false_of_centralizer_le
    {κ : GroupClass} (_hG : IsSQTK κ G)
    [IsSimpleGroup (generalizedFitting G)]
    {T : Sylow 2 G} (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    (d : LargeFamilyObstruction T)
    (hi : ∃ A ∈ d.family, A ≤ (T : Subgroup G) ∧ A ≠ ⊥ ∧
      A ≤ generalizedFitting G)
    {z : G} (hz : orderOf z = 2) (hzL : z ∈ generalizedFitting G)
    (hzT : z ∈ (T : Subgroup G))
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hCM : centralizer ({z} : Set G) ≤ d.overgroup) : False := by
  obtain ⟨_, hsol, A, hA, _, hAL, hcard, hzA, hcomm⟩ :=
    constraints_of_matrix_geometry hp hodd hmodel hLT d hi hz hzL hTz hCM
  have hmod : p % 4 = 1 ∨ p % 4 = 3 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  rcases hmod with hmod | hmod
  · let := d.elementary.1 A hA
    obtain ⟨r, hr, ho, X, hX, hn, hmove⟩ :=
      SemidihedralTorus.escape_of_isPSU (generalizedFitting G)
        hp hodd hmod hmodel T A hcard hAL z hz hzA
    exact hmove (hcomm r hr ho X hX hn)
  · obtain ⟨H, hTH, hH, hmove⟩ :=
      WreathedNormalizer.exists_solvable_sylow_overgroup (generalizedFitting G)
        hLT hp hodd hmod hmodel hz hzL hzT hTz
    exact hmove (hsol H hTH hH)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry
