module
public import ABG.ChapterII.Section2.QDefinitionEquivalence
public import Theory.GroupTheory.PGroup.TrivialImage
public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs
public import ABG.ChapterII.Section1.SmallSubgroups
public import ABG.ChapterII.Section1.WreathedQuaternionCore

/-!
# A quaternion subgroup in the derived subgroup of a Q-group

Every finite group satisfying the enlarged Q predicate contains a quaternion
subgroup of order eight in its derived subgroup. No hypothesis on the full
Sylow subgroup being semidihedral or wreathed is imposed.

The linked overgroup witness supplies an injective map from the actual Sylow
intersection with K onto the largest quaternion subgroup Y, where K has no
normal subgroup of index two. Any two-subgroup of K lies in K': its image in
the abelianization lies in a Sylow two-subgroup, and transfer onto that Sylow
subgroup is a coprime power map. The composite from K is trivial by the
no-normal-index-two hypothesis, so that image is trivial. In the defining
overgroup, the established semidihedral or wreathed quaternion representatives
give Q8 inside Y. Pull it back through the intersection equivalence and map it
into K', then into the ambient derived subgroup.

This proves the quaternion obstruction used at the start of ABG II.5 Lemma 5,
article p.48, `refs/latex/alperin-brauer-gorenstein-pages/page-049.tex`.
The transfer argument replaces the paper's order-three automizer argument
while retaining the entire enlarged definition from II.2 Definition 3.
-/

namespace ABG

private theorem p_subgroup_le_derived {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ p)
    (P : Subgroup G) (hP : IsPGroup p P) : P ≤ commutator G := by
  classical
  let projection : G →* Abelianization G := Abelianization.of
  obtain ⟨S, hS⟩ := (hP.map projection).exists_le_sylow
  have central : Subgroup.normalizer (S : Subgroup (Abelianization G)) ≤
      Subgroup.centralizer (S : Set (Abelianization G)) := by
    intro element _ member _
    exact mul_comm member element
  let transfer := MonoidHom.transferSylow S central
  intro element member
  have image_mem : projection element ∈ S := hS (Subgroup.mem_map.mpr ⟨element, member, rfl⟩)
  have trivial := MonoidHom.eq_one_of_no_normal_index_prime hno S.2
    (transfer.comp projection) element
  have powered : (⟨projection element, image_mem⟩ : S) ^ (S : Subgroup (Abelianization G)).index = 1 := by
    apply Subtype.ext
    have equation := MonoidHom.transferSylow_eq_pow S central (projection element) image_mem
    exact (congrArg Subtype.val equation).symm.trans (congrArg Subtype.val trivial)
  have image_one : (⟨projection element, image_mem⟩ : S) = 1 :=
    (S.2.powEquiv' S.not_dvd_index).injective
      (by simpa using congrArg Subtype.val powered)
  rw [← Abelianization.ker_of G]
  exact congrArg Subtype.val image_one

private theorem largest_contains_quaternion {S : Type*} [Group S]
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S)
    (Y : Subgroup S) (hY : IsLargestQuaternionSubgroup Y) :
    ∃ Q : Subgroup S, Q ≤ Y ∧ IsQuaternionGroup Q := by
  rcases hS with hsemi | ⟨height, hwreathed⟩
  · have finite : Finite S := by
      obtain ⟨exponent, _, hcard, _⟩ := hsemi
      exact Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    let := finite
    obtain ⟨largest, hlarge, _, hmax⟩ := QuasiDihedral.exists_largest_quaternion hsemi
    have equal : largest = Y := (hY.2 largest hlarge).2
      (le_antisymm (hY.2 largest hlarge).1 (Subgroup.card_le_of_le (hmax Y hY.1)))
    obtain ⟨_, Q, _, hQ, _⟩ := QuasiDihedral.four_quaternion_subgroups hsemi
    exact ⟨Q, equal ▸ hmax Q ⟨1, by omega, by simpa using hQ⟩, hQ⟩
  · let : Finite S := Nat.finite_of_card_ne_zero (by rw [hwreathed.2.1]; positivity)
    obtain ⟨presentation⟩ := Wreathed.nonempty_presentation hwreathed
    have equal : presentation.Y = Y := (hY.2 presentation.Y presentation.quaternion_subgroup.1).2
      (le_antisymm (hY.2 presentation.Y presentation.quaternion_subgroup.1).1
        (Subgroup.card_le_of_le (presentation.quaternion_le_Y Y hY.1)))
    have hQ := presentation.quaternion_core_model.1
    exact ⟨presentation.quaternionCore,
      equal ▸ presentation.quaternion_le_Y _
        ⟨1, by omega, by simpa [IsQuaternionGroup] using hQ⟩, hQ⟩

/-- Every finite enlarged Q-group has a quaternion subgroup in its derived subgroup. -/
public theorem qGroup_exists_quaternion_le_commutator
    {H : Type*} [Group H] [Finite H] (hH : IsQGroup H) :
    ∃ Q : Subgroup H, Q ≤ commutator H ∧ IsQuaternionGroup Q := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, instS, hS, R, embedding, Y, K, hinj, hY, _, _, hno, _, hlink⟩ :=
    isQGroup_iff_quaternionOvergroup.mp hH
  let : Group S := instS
  let intersection := K.comap (R : Subgroup H).subtype
  let intoK : intersection →* K :=
    { toFun := fun element => ⟨element.1.1, element.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have intoK_injective : Function.Injective intoK := by
    intro left right equal
    exact Subtype.ext (Subtype.ext (congrArg (fun element : K => (element : H)) equal))
  let equivalence : intersection ≃* Y :=
    (Subgroup.equivMapOfInjective intersection embedding hinj).trans
      (MulEquiv.subgroupCongr hlink)
  obtain ⟨Q, hQY, hQ⟩ := largest_contains_quaternion hS Y hY
  let toY : Q →* Y := Subgroup.inclusion hQY
  let intoH : Q →* H := K.subtype.comp
    (intoK.comp (equivalence.symm.toMonoidHom.comp toY))
  have intoH_injective : Function.Injective intoH :=
    K.subtype_injective.comp (intoK_injective.comp
      (equivalence.symm.injective.comp (Subgroup.inclusion_injective hQY)))
  refine ⟨intoH.range, ?_, ?_⟩
  · have hp : IsPGroup 2 intersection := R.2.to_subgroup intersection
    have derived := p_subgroup_le_derived hno ((⊤ : Subgroup intersection).map intoK)
      ((hp.to_subgroup ⊤).map intoK)
    have mapped : (commutator K).map K.subtype ≤ commutator H := by
      rw [Subgroup.map_subtype_commutator]
      exact Subgroup.commutator_mono le_top le_top
    rintro element ⟨preimage, rfl⟩
    apply mapped
    apply Subgroup.mem_map.mpr
    refine ⟨intoK (equivalence.symm (toY preimage)), ?_, rfl⟩
    exact derived (Subgroup.mem_map.mpr ⟨_, Subgroup.mem_top _, rfl⟩)
  · obtain ⟨model⟩ := hQ
    exact ⟨(MonoidHom.ofInjective intoH_injective).symm.trans model⟩

end ABG
