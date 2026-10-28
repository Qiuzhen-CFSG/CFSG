module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.RadicalQuotient
public import CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity.Source

/-!
# The original nonquasisimple local component modulo its solvable radical

Apply the complete A.3.6 source theorem to the actual component image in
LT/O₂(LT). The original inclusion-induced equivalence and solvable-kernel
transport show that L/O∞(L) is PSL₂(p) for a prime p>3. This is the model
used in 13.1.8(1); identifying it with the action on R₂(N_G(L)) additionally
requires the distinct centralizer statement 13.1.4(5).

Source: Aschbacher--Smith 13.1.4(3), 13.1.8(1), pp.867--869.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]

/-- The structural model for the original radical quotient, with the full
A/C and local-component hypotheses discharged from the source domain. -/
theorem nonquasisimple_local_radical_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (L ⧸ pCore 2 L)) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ClassicalGroup.IsPSL (L ⧸ solvableRadical L) 2 p := by
  have h36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hc := proposition_1_2_1_four_earlier_conclusion h36
    (uniqueness_local_quotient_sqtk hG hL.2.2) hL.1
  exact radical_quotient_pslTwo_of_a36_image L (radicalLocalQuotientEquiv hL) hc hn

end CFSG.Quasithin.Chapter13.Section01
