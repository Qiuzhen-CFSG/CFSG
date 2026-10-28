module

public import ABG.ChapterII.Section1.SmallSubgroups
public import ABG.ChapterII.Section1.FusionPatterns
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# The automizer index of a four-subgroup

For a Klein-four subgroup `T` in a quasi-dihedral Sylow two-subgroup of
a finite group, the ambient index `|N(T):C(T)|` is either two or six.
This proves the four-subgroup index alternatives common to all four
clauses of Alperin--Brauer--Gorenstein, Chapter II, Section 1,
Proposition 1 (article pp. 10--11).

The normalizer acts on `T` with kernel its centralizer. Since the
Klein-four automorphism group has order six, the ambient index divides
six. Lemma II.1.1(ii), applied to the actual subgroup `T.subgroupOf P`,
says its internal centralizer is its center and its normalizer index is
two. A Klein-four group is abelian, so its internal automizer index is
two. Restriction along the subgroup inclusions identifies this index
with the relative index inside the ambient normalizer. Normality of the
centralizer there shows that two divides the ambient index. The two
divisibilities leave exactly two and six.
-/

namespace ABG.QuasiDihedral

variable {G : Type*} [Group G]

private theorem centralizer_subgroupOf (P T : Subgroup G) (hTP : T ≤ P) :
    Subgroup.centralizer (T.subgroupOf P : Set P) =
      (Subgroup.centralizer (T : Set G)).subgroupOf P := by
  ext x
  constructor
  · intro hx
    change (x : G) ∈ Subgroup.centralizer (T : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hx (⟨t, hTP ht⟩ : P) ht)
  · intro hx
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx t ht)

private theorem automizer_dvd_six (T : Subgroup G) [IsKleinFour T] :
    ABG.automizerIndex T ∣ 6 := by
  have h := T.normalizerMonoidHom.range.card_subgroup_dvd_card
  rw [IsKleinFour.card_mulAut T, ← Subgroup.index_ker,
    Subgroup.normalizerMonoidHom_ker] at h
  exact h

/-- The normalizer-to-centralizer index of a four-subgroup in a quasi-dihedral
Sylow two-subgroup is two or six. -/
public theorem four_automizer_index [Finite G] (P : Sylow 2 G)
    (hP : Stellmacher.IsSemidihedralGroup P) (T : Subgroup G)
    (hTP : T ≤ P) (hT : IsKleinFour T) :
    ABG.automizerIndex T = 2 ∨ ABG.automizerIndex T = 6 := by
  let := hT
  let U := T.subgroupOf (P : Subgroup G)
  let e := Subgroup.subgroupOfEquivOfLe hTP
  have hU : IsKleinFour U := {
    card_four := (Nat.card_congr e.toEquiv).trans hT.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e).trans hT.exponent_two }
  let := hU
  obtain ⟨_, _, _, _, _, _, hlocal⟩ := four_quaternion_subgroups hP
  obtain ⟨hC, hN⟩ := hlocal U (Or.inl hU)
  let : IsMulCommutative U := IsKleinFour.isMulCommutative
  rw [Subgroup.center_eq_top, ← MonoidHom.range_eq_map, U.range_subtype] at hC
  have hi : (Subgroup.centralizer (U : Set P)).relIndex
      (Subgroup.normalizer (U : Set P)) = 2 := by rwa [hC]
  rw [show U = T.subgroupOf (P : Subgroup G) from rfl,
    centralizer_subgroupOf _ _ hTP, ← Subgroup.subgroupOf_normalizer_eq hTP] at hi
  let N := Subgroup.normalizer (T : Set G)
  let C := Subgroup.centralizer (T : Set G)
  have heq : (C.subgroupOf (P : Subgroup G)).relIndex (N.subgroupOf (P : Subgroup G)) =
      (C.subgroupOf N).relIndex ((P : Subgroup G).subgroupOf N) := by
    simp only [Subgroup.subgroupOf, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq, Subgroup.range_subtype]
    rw [inf_comm N]
  have hdiv : 2 ∣ ABG.automizerIndex T := by
    rw [← hi, heq]
    exact Subgroup.relIndex_dvd_index_of_normal
      (C.subgroupOf N) ((P : Subgroup G).subgroupOf N)
  have hsix := automizer_dvd_six T
  have hle := Nat.le_of_dvd (by decide : 0 < 6) hsix
  interval_cases hi' : ABG.automizerIndex T <;> simp_all

end ABG.QuasiDihedral
