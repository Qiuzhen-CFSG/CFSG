module
public import ABG.ChapterII.Section2.QNormalWitness
public import ABG.ChapterII.Section3.FullQCentralSylowQuotient

/-!
# Central Sylow quotients of enlarged Q-groups

Let G be a finite Q-group, with a prescribed semidihedral or wreathed
Sylow two-subgroup S. If Z(S) is central in G and the odd core of G is
trivial, quotienting by the ambient image N of Z(S) gives dihedral Sylow
two-subgroups and trivial odd core. The subgroup N is nontrivial cyclic,
and the quotient has a normal subgroup of index two with no normal
subgroup of index two.

The enlarged-Q witness extraction supplies a normal subgroup K with
quaternion Sylow subgroups and index |Z(S)|. Centrality makes N normal. The shared quotient
construction uses |K intersect N| = 2 to compute the index of the image of
K; absence of index-two normal subgroups descends along its quotient map.
The dihedral Sylow and odd-core clauses use the previously proved quotient
transfer theorems. This is the central quotient step of ABG II.3
Proposition 2, article p22 of the Alperin--Brauer--Gorenstein paper.
-/

namespace ABG
variable {G : Type*} [Group G] [Finite G]

/-- The central quotient data for any prescribed full Sylow subgroup of an
enlarged Q-group with trivial odd core. -/
public theorem qGroup_central_sylow_quotient_data
    (hQ : IsQGroup G) (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S)
    (hcentral : subgroupCenter (S : Subgroup G) ≤ Subgroup.center G)
    (hcore : pPrimeCore 2 G = ⊥) :
    ∃ (N : Subgroup G) (hNnormal : N.Normal),
      letI := hNnormal
      N = subgroupCenter (S : Subgroup G) ∧ IsCyclic N ∧ N ≠ ⊥ ∧
        GorensteinWalter.HasDihedralSylowTwo (G ⧸ N) ∧
        pPrimeCore 2 (G ⧸ N) = ⊥ ∧
        ∃ J : Subgroup (G ⧸ N), J.Normal ∧ J.index = 2 ∧ HasNoNormalIndexTwoSubgroup J := by
  obtain ⟨K, hKn, hK, hno, hi⟩ := qGroup_exists_normal_quaternion_witness hQ S hS
  let := hKn
  let N := subgroupCenter (S : Subgroup G)
  have hNnormal : N.Normal := by
    constructor
    intro x hx g
    have hxg := Subgroup.mem_center_iff.mp (hcentral hx) g
    simpa [hxg, mul_assoc] using hx
  let := hNnormal
  exact ⟨N, hNnormal, rfl,
    central_sylow_quotient_data_of_normal_quaternion S K N hS hK hno hi rfl hcentral hcore⟩

end ABG
