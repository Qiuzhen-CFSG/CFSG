module
public import Theory.GroupTheory.SpecificGroups.QuaternionEightAut
public import ABG.ChapterII.Section1.SmallSubgroups
public import ABG.ChapterII.Section1.FusionPatterns
public import Theory.GroupTheory.NormalizerInnerAutomorphisms
public import Theory.GroupTheory.NormalizerFusionIndexControl

/-!
# The outer automizer index of a quaternion subgroup

Let `P` be a quasi-dihedral Sylow two-subgroup of a finite group, and let
`Q ≤ P` be a quaternion subgroup of order eight. Then the outer automizer
index `|N_G(Q) : Q C_G(Q)|` is either two or six. This supplies the quaternion
index alternatives common to all four clauses of Alperin–Brauer–Gorenstein,
Chapter II, §1, Proposition 1, article pp. 10–11, in
`refs/latex/alperin-brauer-gorenstein.tex`.

The normalizer action contains every inner automorphism of `Q`. The preimage
of the inner automorphism subgroup is exactly `Q C_G(Q)`, so the outer
index divides the index six of inner automorphisms in the full automorphism
group of the quaternion group. The explicit isomorphism with `QuaternionGroup 2`
transports that index without changing the subgroup or its action.

Lemma II.1.1(ii) gives `C_P(Q) ≤ Q` and `|N_P(Q):Q| = 2`. Since `Q ≤ P`,
the first assertion makes `Q C_G(Q) ∩ P = Q`: write an element as a product
of a quaternion element and a centralizing element. Restricting the ambient
index to the Sylow normalizer therefore gives two. The denominator is normal
in the ambient normalizer, so this restricted index divides the ambient one.
The two divisibilities leave precisely two and six.
-/

namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]
private theorem denominator_normal (Q : Subgroup G) :
    ((Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf (Subgroup.normalizer (Q : Set G))).Normal := by
  rw [Subgroup.subgroupOf_sup Q.le_normalizer (Subgroup.centralizer_le_normalizer _)]
  infer_instance

private theorem outer_dvd_six (Q : Subgroup G) (e : Q ≃* QuaternionGroup 2) :
    ABG.outerAutomizerIndex Q ∣ 6 := by
  have hle : (MulAut.conj : Q →* MulAut Q).range ≤ Q.normalizerMonoidHom.range := by
    rintro f ⟨x,rfl⟩
    refine ⟨⟨x.val,Q.le_normalizer x.property⟩,?_⟩
    ext y
    rfl
  rw [ABG.outerAutomizerIndex,Subgroup.relIndex,
    ←Subgroup.normalizerMonoidHom_comap_conj_range,Subgroup.index_comap,
    ←QuaternionGroup.index_range_conj_of_equiv e]
  exact Subgroup.relIndex_dvd_index_of_le hle

/-- A quaternion subgroup in a quasi-dihedral Sylow two-subgroup has outer automizer index two or six. -/
public theorem quaternion_outer_automizer_index [Finite G] (P : Sylow 2 G)
    (hP : Stellmacher.IsSemidihedralGroup P) (Q : Subgroup G)
    (hQP : Q ≤ P) (hQ : Nonempty (Q ≃* QuaternionGroup 2)) :
    ABG.outerAutomizerIndex Q=2 ∨ ABG.outerAutomizerIndex Q=6 := by
  obtain ⟨eQ⟩ := hQ
  let U := Q.subgroupOf (P : Subgroup G)
  let e := Subgroup.subgroupOfEquivOfLe hQP
  have hU : Nonempty (U ≃* QuaternionGroup 2) := ⟨e.trans eQ⟩
  obtain ⟨_,_,_,_,_,_,hlocal⟩ := four_quaternion_subgroups hP
  obtain ⟨hC,hN⟩ := hlocal U (Or.inr hU)
  have hCP : (Subgroup.centralizer (Q : Set G)).subgroupOf (P : Subgroup G) ≤ U := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (U : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx t ht)
    rw [hC] at hxC
    exact Subgroup.map_subtype_le _ hxC
  have hi : ((Q ⊔ Subgroup.centralizer (Q : Set G)).subgroupOf (P : Subgroup G)).relIndex
      ((Subgroup.normalizer (Q : Set G)).subgroupOf (P : Subgroup G))=2 := by
    rw [Subgroup.sup_centralizer_subgroupOf_eq_of_centralizer_le _ _ hQP hCP,Subgroup.subgroupOf_normalizer_eq hQP]
    exact hN
  let N := Subgroup.normalizer (Q : Set G)
  let D := Q ⊔ Subgroup.centralizer (Q : Set G)
  have heq : (D.subgroupOf (P : Subgroup G)).relIndex (N.subgroupOf (P : Subgroup G)) =
      (D.subgroupOf N).relIndex ((P : Subgroup G).subgroupOf N) := by
    simp only [Subgroup.subgroupOf,Subgroup.relIndex_comap,
      Subgroup.map_comap_eq,Subgroup.range_subtype]
    rw [inf_comm N]
  let : (D.subgroupOf N).Normal := denominator_normal Q
  have hdiv : 2 ∣ ABG.outerAutomizerIndex Q := by
    rw [←hi,heq]
    exact Subgroup.relIndex_dvd_index_of_normal
      (D.subgroupOf N) ((P : Subgroup G).subgroupOf N)
  have hsix := outer_dvd_six Q eQ
  have hle := Nat.le_of_dvd (by decide : 0 < 6) hsix
  interval_cases hi' : ABG.outerAutomizerIndex Q <;> simp_all
end ABG.QuasiDihedral
