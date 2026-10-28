module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.WreathedNormalizer.Movement
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.WreathedNormalizer.Solvability
public import Theory.GroupTheory.SolvableNormalizerExtension
public import Theory.GroupTheory.SylowNormalRestriction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.Reduction

/-!
# A solvable Sylow overgroup moving an inner PSU₃ involution

Let L be simple normal PSU₃(p), p congruent to three modulo four, and G=LT
for the specified Sylow two-subgroup T. The Sylow intersection in L has a
characteristic abelian index-two base A. Its intrinsic normalizer is solvable
by the determinant-one weight calculation and moves the central involution
by the full Frattini action. Characteristicity puts all of T in N_G(A).
The quotient G/L is a two-group, so N_G(A) is solvable as well.

The construction includes p=3, arbitrary Hermitian models and every ambient
two-extension. Neither SQTK nor centralizer maximality is needed to construct H.
The final application contradicts the actual solvable-overgroup clause of
InnerGeometry.constraints_of_intrinsic_coatom; its coatom premise is kept
only in that separate consumer.

Source: Aschbacher--Smith E.1.14(7), printed p.214, and A.3.21, pp.55--56;
Aschbacher, GF(2)-representations of finite groups (1982), Lemma 4.11.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.WreathedNormalizer

variable {G : Type*} [Group G] [Finite G]

/-- For every simple normal PSU₃(p) socle with p congruent to three modulo four,
the characteristic base normalizer is a solvable overgroup of the specified
ambient Sylow and moves its central involution. No SQTK hypothesis is needed. -/
theorem exists_solvable_sylow_overgroup
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] {T : Sylow 2 G}
    (hLT : L ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hmod : p % 4 = 3)
    (hmodel : ClassicalGroup.IsPSU L 3 p)
    {z : G} (hz : orderOf z = 2) (hzL : z ∈ L) (hzT : z ∈ (T : Subgroup G))
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    ∃ H : Subgroup G, (T : Subgroup G) ≤ H ∧ Group.IsSolvable H ∧
      ¬ H ≤ centralizer ({z} : Set G) := by
  have hsol := intrinsicSolvability_of_isPSU hp hodd hmod hmodel
  have hmove := intrinsicMovement_of_isPSU hp hodd hmod hmodel
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal L
  obtain ⟨A, ha, hi, hchar⟩ := exists_characteristic_abelian_base hp hodd hmod hmodel S
  let := hchar
  let B := A.map (S : Subgroup L).subtype
  let H := normalizer (B.map L.subtype : Set G)
  have hT : (T : Subgroup G) ≤ H :=
    sylow_le_normalizer_characteristic_intersection L T S
      (by rw [hS, subgroupOf_map_subtype]) A
  let : Group.IsNilpotent (G ⧸ L) :=
    (isPGroup_quotient_of_sup_eq_top L T T.isPGroup' hLT).isNilpotent
  let : Group.IsSolvable (normalizer (B : Set L)) := hsol S A ha hi
  have hH : Group.IsSolvable H := normalizer_map_subtype_isSolvable L B
  let zl : L := ⟨z, hzL⟩
  have hzl : zl ∈ (S : Subgroup L) := by rw [hS]; exact hzT
  let zs : (S : Subgroup L) := ⟨zl, hzl⟩
  have hzs : orderOf zs = 2 := by
    simpa only [zs, zl, orderOf_mk] using hz
  have hzc : zs ∈ center S := by
    apply mem_center_iff.mpr
    intro s
    apply Subtype.ext
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hTz (show (s.val : G) ∈ (T : Subgroup G) from
      (show s.val ∈ (T : Subgroup G).subgroupOf L from hS ▸ s.property)))
  exact ⟨H, hT, hH, normalizer_image_not_le_centralizer L B zl
    (hmove S A ha hi zs hzs hzc)⟩
/-- Actual E.1.14 consumer: the constructed solvable overgroup contradicts
the solvable-overgroup clause of `constraints_of_intrinsic_coatom`.
The centralizer-coatom hypothesis belongs to that source consumer, not to
the preceding construction of the moving overgroup. -/
theorem false_of_intrinsic_coatom
    [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hmod : p % 4 = 3)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (d : LargeFamilyObstruction T)
    (hi : ∃ A ∈ d.family, A ≤ (T : Subgroup G) ∧ A ≠ ⊥ ∧ A ≤ generalizedFitting G)
    {z : G} (hz : orderOf z = 2) (hzL : z ∈ generalizedFitting G)
    (hzT : z ∈ (T : Subgroup G))
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hCM : centralizer ({z} : Set G) ≤ d.overgroup)
    (hmax : IsCoatom ((centralizer ({z} : Set G)).subgroupOf (generalizedFitting G))) : False := by
  obtain ⟨H, hTH, hH, hm⟩ := exists_solvable_sylow_overgroup
    (generalizedFitting G) hLT hp hodd hmod hmodel hz hzL hzT hTz
  exact hm ((constraints_of_intrinsic_coatom hp hodd hmodel hLT d hi hz hzL hTz hCM hmax).2.1
    H hTH hH)
end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.WreathedNormalizer
