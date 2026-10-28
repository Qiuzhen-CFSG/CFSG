module
public import ABG.ChapterII.Section1.WreathedFusion
public import ABG.ChapterII.Section2.Defs
public import ABG.ChapterII.Section1.FocalIndexTwo
public import ABG.ChapterII.Section5.QDerivedQuaternion
public import Theory.GroupTheory.QuaternionSectionExclusion

/-!
# D-groups have no Q-group section

For a finite D-group H, every section is a quotient of a subgroup A by a
normal subgroup N. The proved fusion alternatives place H' inside a subgroup
whose Sylow two-subgroup is dihedral or abelian. A Q-group section contains a
quaternion subgroup in its own derived subgroup; pulling that subgroup back
through A → A/N and then into H' produces a quaternion section of the
container, contradicting the independent dihedral/abelian obstruction.

This follows ABG Chapter II, Section 5, Lemma 5, article p. 48 / PDF p. 49,
`refs/latex/alperin-brauer-gorenstein-pages/page-049.tex`. The proof handles
the enlarged Q-group definition and genuine sections, not just subgroups.
The direct container argument packages the odd-kernel/derived transfer in the
pullback construction.
-/

namespace ABG
universe u
variable {G : Type u} [Group G] [Finite G]

theorem dGroup_derived_container (hD : IsDGroup G) :
    ∃ K : Subgroup G, commutator G ≤ K ∧
      (HasDihedralSylowTwo K ∨ ∃ R : Sylow 2 K, IsMulCommutative R) := by
  rcases hD with (⟨S, T, Q, _, hpattern⟩ | ⟨S, n, U, V, hframe, hpattern⟩) |
    ⟨hdihedral, _⟩
  · obtain ⟨K, hnormal, hindex, hK, _⟩ := hpattern.1
    let := hnormal
    exact ⟨K, derived_le_index_two K hindex, Or.inl hK⟩
  · obtain ⟨P⟩ := Wreathed.nonempty_presentation hframe.1
    obtain ⟨hU, element, hVconj⟩ := hframe.presentation_representatives P
    have hV : outerAutomizerIndex V =
        outerAutomizerIndex (P.V.map (S : Subgroup G).subtype) := by
      rw [← hVconj]
      exact outerAutomizerIndex_map _ (MulAut.conj (element : G))
    have hfocal := (Wreathed.focal_subgroup_cases S P).2.2.1
      (hU ▸ hpattern.2.2.1) (hV.symm.trans hpattern.2.2.2)
    obtain ⟨K, hnormal, hindex, _, R, hR, _⟩ :=
      exists_normal_index_two_sylow_of_focalSubgroupOf S P.U P.index_U hfocal
    let := hnormal
    have hmap : (R : Subgroup K).map K.subtype = U := hR.trans hU.symm
    let : IsMulCommutative U := hframe.2.2.1
    have hcomm : IsMulCommutative ((R : Subgroup K).map K.subtype) := hmap ▸ inferInstance
    let := hcomm
    let equivalence := (R : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective
    have : IsMulCommutative R := ⟨⟨fun left right => equivalence.injective (by
      simp only [map_mul, mul_comm'])⟩⟩
    exact ⟨K, derived_le_index_two K hindex, Or.inr ⟨R, this⟩⟩
  · obtain ⟨S, hS⟩ := hdihedral
    let equivalence : G ≃* (⊤ : Subgroup G) := (Subgroup.topEquiv).symm
    let R := S.mapSurjective (f := equivalence.toMonoidHom) equivalence.surjective
    have hR : Stellmacher.IsDihedralGroup R := by
      obtain ⟨height, ⟨model⟩⟩ := hS
      exact ⟨height, ⟨((S : Subgroup G).equivMapOfInjective equivalence.toMonoidHom
        equivalence.injective).symm.trans model⟩⟩
    exact ⟨⊤, le_top, Or.inl ⟨R, hR⟩⟩

omit [Finite G] in
theorem derived_section_lift {H : Type*} [Group H]
    (A : Subgroup G) (projection : A →* H) (onto : Function.Surjective projection)
    (Q : Subgroup H) (derived : Q ≤ commutator H) :
    ∃ B : Subgroup G, B ≤ commutator G ∧
      ∃ lifted : B →* Q, Function.Surjective lifted := by
  have mapped : (commutator A).map projection = commutator H := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr onto]
    rfl
  let inclusion : commutator A →* G := A.subtype.comp (commutator A).subtype
  have injective : Function.Injective inclusion :=
    A.subtype_injective.comp (commutator A).subtype_injective
  let restricted : commutator A →* H := projection.comp (commutator A).subtype
  let preimage : Subgroup (commutator A) := Q.comap restricted
  let lift : preimage →* Q := {
    toFun := fun element => ⟨restricted element.1, element.2⟩
    map_one' := Subtype.ext (map_one restricted)
    map_mul' := fun left right => Subtype.ext (map_mul restricted left.1 right.1) }
  have lift_onto : Function.Surjective lift := by
    intro element
    have member : element.1 ∈ (commutator A).map projection := mapped ▸ derived element.2
    obtain ⟨representative, hrepresentative, image⟩ := member
    refine ⟨⟨⟨representative, hrepresentative⟩, ?_⟩, Subtype.ext image⟩
    change projection representative ∈ Q
    rw [image]
    exact element.2
  let B := preimage.map inclusion
  let equivalence : preimage ≃* B := preimage.equivMapOfInjective inclusion injective
  refine ⟨B, ?_, lift.comp equivalence.symm.toMonoidHom,
    lift_onto.comp equivalence.symm.surjective⟩
  rintro element ⟨representative, _, rfl⟩
  have member : (representative.1 : G) ∈ (commutator A).map A.subtype :=
    ⟨representative.1, representative.2, rfl⟩
  rw [Subgroup.map_subtype_commutator] at member
  exact Subgroup.commutator_mono le_top le_top member

public theorem dGroup_no_qGroup_section
    (hD : IsDGroup G) (A : Subgroup G) (N : Subgroup A) [N.Normal] :
    ¬ IsQGroup (A ⧸ N) := by
  intro hQ
  obtain ⟨Q, derived, ⟨quaternion_equivalence⟩⟩ :=
    qGroup_exists_quaternion_le_commutator hQ
  obtain ⟨B, hB, projection, onto⟩ := derived_section_lift A (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) Q derived
  obtain ⟨K, hK, shape⟩ := dGroup_derived_container hD
  let equivalence : B.subgroupOf K ≃* B := Subgroup.subgroupOfEquivOfLe (hB.trans hK)
  let final_projection : B.subgroupOf K →* QuaternionGroup 2 :=
    quaternion_equivalence.toMonoidHom.comp (projection.comp equivalence.toMonoidHom)
  exact no_quaternion_section_of_dihedral_or_abelian_sylow K shape
    (B.subgroupOf K) final_projection
    (quaternion_equivalence.surjective.comp (onto.comp equivalence.surjective))

end ABG
