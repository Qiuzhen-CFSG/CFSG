module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry
public import Theory.Representation.BinaryPermutationSixCover.Universal
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.BinaryOffender.RestrictionComparison
public import Theory.Representation.BinaryOffender.QuadraticQuotient

/-!
# Fixed index on the full six-letter augmentation cover

The canonical Sylow subgroup fixes the constant vector and the vector of its
invariant pair. These independent vectors give fixed codimension at most three.
Sylow containment and conjugacy give the same bound for every two-subgroup.
The whole five-dimensional cover is retained; its constant line is not removed.
The native replacement application is in NativeBounds.

Source: MS93 (3.6), printed p.871, the bound |Z_alpha : Z_beta| = 2^3;
Aschbacher--Smith I.1.5--6, the six-letter augmentation cover.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement

private def constantVector : core (Fin 6) :=
  ⟨allOne (Fin 6), by change (∑ _ : Fin 6, (1 : ZMod 2)) = 0; decide⟩
private def pairVector : core (Fin 6) :=
  ⟨Pi.single 4 1 + Pi.single 5 1, by simp [mem_core, Finset.sum_add_distrib]; decide⟩

private theorem pair_fixed (g : S) (hg : g ∈ H1) :
    coreRepresentation (Fin 6) g pairVector = pairVector := by
  have hi := mem_H1_cases (H1.inv_mem hg)
  apply Subtype.ext
  funext i
  change ((Pi.single 4 (1 : ZMod 2) + Pi.single 5 1) : Fin 6 → ZMod 2) (g⁻¹ i) =
    ((Pi.single 4 (1 : ZMod 2) + Pi.single 5 1) : Fin 6 → ZMod 2) i
  have ht : g⁻¹ i = 4 ∨ g⁻¹ i = 5 ↔ i = 4 ∨ i = 5 := by
    rcases hi with ⟨h4,h5⟩ | ⟨h4,h5⟩
    · constructor
      · rintro (hh | hh)
        · exact Or.inl ((g⁻¹).injective (hh.trans h4.symm))
        · exact Or.inr ((g⁻¹).injective (hh.trans h5.symm))
      · rintro (rfl | rfl)
        · exact Or.inl h4
        · exact Or.inr h5
    · constructor
      · rintro (hh | hh)
        · exact Or.inr ((g⁻¹).injective (hh.trans h5.symm))
        · exact Or.inl ((g⁻¹).injective (hh.trans h4.symm))
      · rintro (rfl | rfl)
        · exact Or.inr h4
        · exact Or.inl h5
  have hp (j : Fin 6) :
      ((Pi.single 4 (1 : ZMod 2) + Pi.single 5 1) : Fin 6 → ZMod 2) j =
        if j = 4 ∨ j = 5 then 1 else 0 := by fin_cases j <;> decide
  simp only [hp,ht]

private theorem core_fixed_two :
    2 ≤ Module.finrank (ZMod 2)
      (fixedSpace (coreRepresentation (Fin 6)) (H1 ⊓ H2)) := by
  let c : fixedSpace (coreRepresentation (Fin 6)) (H1 ⊓ H2) :=
    ⟨constantVector, fun g => Subtype.ext (permute_allOne (Fin 6) g)⟩
  let p : fixedSpace (coreRepresentation (Fin 6)) (H1 ⊓ H2) :=
    ⟨pairVector, fun g => pair_fixed g g.property.1⟩
  have hi : LinearIndependent (ZMod 2) ![c,p] := by
    apply LinearIndependent.of_comp (fixedSpace (coreRepresentation (Fin 6)) (H1 ⊓ H2)).subtype
    have he : (fixedSpace (coreRepresentation (Fin 6)) (H1 ⊓ H2)).subtype ∘ ![c,p] =
        ![constantVector,pairVector] := by funext i; fin_cases i <;> rfl
    rw [he]
    rw [Fintype.linearIndependent_iff]
    decide +kernel
  simpa using hi.fintype_card_le_finrank

/-- Every two-subgroup has fixed codimension at most three on the entire
six-letter augmentation cover. -/
theorem core_fixedCodim_le_three (A : Subgroup S) (hA : IsPGroup 2 A) :
    fixedCodim (coreRepresentation (Fin 6)) A ≤ 3 := by
  obtain ⟨P,hP⟩ := hA.exists_le_sylow
  obtain ⟨g,hg,_⟩ := NaturalGeometry.sylow_flag P
  have ht := fixedCodim_add_finrank (coreRepresentation (Fin 6)) (H1 ⊓ H2)
  rw [finrank_core] at ht
  have htwo := core_fixed_two
  have hc : fixedCodim (coreRepresentation (Fin 6)) (P : Subgroup S) ≤ 3 := by
    rw [←hg,fixedCodim_map_conj]
    norm_num only [Fintype.card_fin,Nat.reduceSub] at ht
    omega
  have hf := Submodule.finrank_mono
    (fixedSpace_antitone (coreRepresentation (Fin 6)) hP)
  have hAP := fixedCodim_add_finrank (coreRepresentation (Fin 6)) A
  have hPP := fixedCodim_add_finrank (coreRepresentation (Fin 6)) (P : Subgroup S)
  omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement
