module

public import Theory.Character.Peterfalvi1.MackeyCore
public import Theory.Character.CharacterValues

noncomputable section
open scoped BigOperators
attribute [local instance] Fintype.ofFinite
namespace Section2
universe u

public theorem inducedCF_isVirtualCharacter_of_virtualCharacter
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) [Finite S] {ψ : Section1.ClassFunction S}
    (hψ : IsVirtualCharacter ψ) :
    IsVirtualCharacter (Section1.inducedCF S ψ) := by
  classical
  rcases hψ with ⟨r, m, n, ρ, rfl⟩
  refine ⟨r, m, fun i => Module.finrank ℂ (Representation.IndV S.subtype (ρ i)),
    fun i => Section1.standardizeRepresentation (Representation.ind S.subtype (ρ i)), ?_⟩
  ext g
  change Section1.inducedCF S
      (virtualCharacterOfRepresentations r m n ρ) g =
    ∑ i : Fin r, (m i : ℂ) *
      (Section1.standardizeRepresentation (Representation.ind S.subtype (ρ i))).character g
  have hvirtual :
      virtualCharacterOfRepresentations r m n ρ =
        Section1.weightedFamilySum (fun i : Fin r => (m i : ℂ))
          (fun i : Fin r => (ρ i).character) := by
    funext g
    have huniv :
        (@Finset.univ (Fin r) (Fin.fintype r)) =
          (@Finset.univ (Fin r) (Fintype.ofFinite (Fin r))) := by
      ext i
      simp
    unfold virtualCharacterOfRepresentations Section1.weightedFamilySum
    simp
    rw [huniv]
  calc
    Section1.inducedCF S (virtualCharacterOfRepresentations r m n ρ) g =
        Section1.weightedFamilySum (fun i : Fin r => (m i : ℂ))
          (fun i : Fin r => Section1.inducedCF S ((ρ i).character)) g := by
          have hlin :
              Section1.inducedCF S (virtualCharacterOfRepresentations r m n ρ) =
                Section1.weightedFamilySum (fun i : Fin r => (m i : ℂ))
                  (fun i : Fin r => Section1.inducedCF S ((ρ i).character)) := by
            calc
              Section1.inducedCF S (virtualCharacterOfRepresentations r m n ρ) =
                  Section1.inducedCF S (Section1.weightedFamilySum
                    (fun i : Fin r => (m i : ℂ)) (fun i : Fin r => (ρ i).character)) :=
                congrArg (Section1.inducedCF S) hvirtual
              _ = Section1.weightedFamilySum (fun i : Fin r => (m i : ℂ))
                    (fun i : Fin r => Section1.inducedCF S ((ρ i).character)) :=
                Section1.inducedCF_weightedFamilySum S
                  (fun i : Fin r => (m i : ℂ)) (fun i : Fin r => (ρ i).character)
          simpa using congrFun hlin g
    _ = ∑ i : Fin r, (m i : ℂ) *
          (Section1.standardizeRepresentation (Representation.ind S.subtype (ρ i))).character g := by
          have huniv :
              (@Finset.univ (Fin r) (Fin.fintype r)) =
                (@Finset.univ (Fin r) (Fintype.ofFinite (Fin r))) := by
            ext i
            simp
          rw [Section1.weightedFamilySum]
          rw [huniv]
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [Section1.standardizeRepresentation_character,
            Section1.inducedCF_eq_representation_character]

end Section2
