module

public import Theory.GroupTheory.Recognition.ReeTwo.TransferReduction
public import Theory.SpecificGroups.ReeTwo.Characters
public import Theory.GroupTheory.CentricCharacterFusion
public import Theory.GroupTheory.Recognition.ReeTwo.CentricNormalizerCharacters

/-!
# Ambient fusion obstruction for the Ree two centralizer

The character on the concrete centralizer restricts to the parity character
under the precise Sylow equivalence chosen in `TransferReduction`. Although
that equivalence uses a choice of Sylow conjugator, homomorphisms to an abelian
group are unchanged by this conjugation.

The centric normalizer analysis supplies a common nontrivial binary character,
and centric fusion transport makes that character invariant under ambient
conjugacy. Ordinary transfer then contradicts nonsolvable simplicity. This
also gives the requested root-1 fusion separation, without requiring that the
original parity character itself be invariant under all ambient fusion.

Source: Shinoda (1975), pp. 79 and 83--85, and Parrott (1973), pp. 341--357.
The alternative character route follows the fusion obstruction in van Beek
(2024), Proposition 3.1, p. 10, using the proved centric normalizer analysis.
-/

namespace ReeTwo

/-- The chosen Sylow equivalence transports the restriction of the actual
centralizer character to the model parity character. -/
public theorem character_sylowEquivOfCentralizer
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (z : G)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (ec : Subgroup.centralizer {z} ≃* Centralizer) (x : S) :
    SylowModel.character (sylowEquivOfCentralizer S z hcentral ec x) =
      Centralizer.character (ec ⟨x, hcentral x.property⟩) := by
  simpa only [Centralizer.character_embedding] using
    abelianCharacter_sylowEquivOfCentralizer Centralizer.character S z hcentral ec x

/-- Conjugation in the given involution centralizer preserves the transported
parity character on the ambient Sylow subgroup. -/
public theorem character_eq_of_conjugator_mem_centralizer
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (z : G)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (ec : Subgroup.centralizer {z} ≃* Centralizer)
    {x y : S} {g : G} (hg : g ∈ Subgroup.centralizer {z})
    (hxy : g * (x : G) * g⁻¹ = (y : G)) :
    SylowModel.character (sylowEquivOfCentralizer S z hcentral ec x) =
      SylowModel.character (sylowEquivOfCentralizer S z hcentral ec y) := by
  simpa only [Centralizer.character_embedding] using
    abelianCharacter_eq_of_conjugator_mem_centralizer Centralizer.character
      S z hcentral ec hg hxy

/-- A conjugator taking transported root 1 into the parity kernel cannot lie
in the given involution centralizer. This is only the internal fusion exclusion. -/
public theorem rootOne_fusion_conjugator_not_mem_centralizer
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (z : G)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (ec : Subgroup.centralizer {z} ≃* Centralizer) (t : S)
    (ht : SylowModel.character (sylowEquivOfCentralizer S z hcentral ec t) = 1)
    (g : G)
    (hg : g * (((sylowEquivOfCentralizer S z hcentral ec).symm
      SylowModel.rootOne : S) : G) * g⁻¹ = (t : G)) :
    g ∉ Subgroup.centralizer {z} := by
  intro hcentralizer
  have h := character_eq_of_conjugator_mem_centralizer S z hcentral ec hcentralizer hg
  rw [MulEquiv.apply_symm_apply, ht] at h
  exact SylowModel.character_rootOne_ne_one h

/-- The actual Ree two involution centralizer supplies a nontrivial binary
character on its identified Sylow subgroup that respects ambient fusion.
No simplicity or local solvability hypothesis is required. -/
public theorem exists_nontrivial_fusion_invariant_character_of_centralizer
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (z : G)
    (hz : orderOf z = 2)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (ec : Subgroup.centralizer {z} ≃* Centralizer) :
    let e := sylowEquivOfCentralizer S z hcentral ec
    ∃ χ : SylowModel →* FiveFour.Cyclic 2,
      (∃ x, χ x ≠ 1) ∧
        ∀ x y : S, IsConj (x : G) (y : G) → χ (e x) = χ (e y) := by
  obtain ⟨χ, hnontrivial, hlocal⟩ :=
    exists_common_centricNormalizer_character S z hz hcentral ec
  refine ⟨χ, hnontrivial, ?_⟩
  intro x y hxy
  exact S.centric_character_fusion
    (χ.comp (sylowEquivOfCentralizer S z hcentral ec).toMonoidHom) hlocal hxy

/-- Under nonsolvable simplicity, no ambient conjugate of transported root 1
can lie in the original parity kernel. This follows by transfer from the
common fusion-invariant character, which may differ from the parity map. -/
public theorem rootOne_fusion_character_ne_one
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G) (z : G)
    (hz : orderOf z = 2)
    (hcentral : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (ec : Subgroup.centralizer {z} ≃* Centralizer) (t : S) :
    let e := sylowEquivOfCentralizer S z hcentral ec
    IsConj ((e.symm SylowModel.rootOne : S) : G) (t : G) →
      SylowModel.character (e t) ≠ 1 := by
  obtain ⟨χ, hnontrivial, hrespect⟩ :=
    exists_nontrivial_fusion_invariant_character_of_centralizer S z hz hcentral ec
  exact (false_of_fusion_invariant_character hns S
    (sylowEquivOfCentralizer S z hcentral ec) χ hnontrivial hrespect).elim

end ReeTwo
