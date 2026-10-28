module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.Reduction

/-!
# Applying the odd torus to the original inner-family obstruction

The intrinsic-coatom reduction supplies an actual four-group from the original
family and forces every odd-prime commutator normalized by its full C_T(A) into
C_G(z). The concrete unitary torus contradicts exactly that containment when
p is congruent to one modulo four. No coordinate, torus-normalization or
escaping-subgroup premise remains.

The centralizer-coatom and ambient centralizer-containment hypotheses remain
with the inner-geometry assembly; this application does not assert the full
E.1.14(7). Source: Aschbacher--Smith, printed p.214, and Aschbacher (1982),
Lemma 4.11.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus

variable {G : Type*} [Group G] [Finite G]

/-- The semidihedral torus discharges the odd-commutator model input of
`constraints_of_intrinsic_coatom` on the literal original inner actor. -/
theorem false_of_intrinsic_coatom_mod_four_one
    [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hmod : p % 4 = 1)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (d : LargeFamilyObstruction T)
    (hi : ∃ A ∈ d.family, A ≤ (T : Subgroup G) ∧ A ≠ ⊥ ∧
      A ≤ generalizedFitting G)
    {z : G} (hz : orderOf z = 2) (hzL : z ∈ generalizedFitting G)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hCM : centralizer ({z} : Set G) ≤ d.overgroup)
    (hmax : IsCoatom ((centralizer ({z} : Set G)).subgroupOf
      (generalizedFitting G))) : False := by
  obtain ⟨_, _, A, hA, _, hAL, hcard, hzA, hcomm⟩ :=
    constraints_of_intrinsic_coatom hp hodd hmodel hLT d hi hz hzL hTz hCM hmax
  let := d.elementary.1 A hA
  obtain ⟨r, hr, ho, X, hX, hn, hescape⟩ :=
    escape_of_isPSU (generalizedFitting G) hp hodd hmod hmodel T A hcard hAL z hz hzA
  exact hescape (hcomm r hr ho X hX hn)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus
