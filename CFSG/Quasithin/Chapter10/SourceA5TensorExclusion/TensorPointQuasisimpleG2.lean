module

public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointQuasisimpleSource
public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.G2.FourBound
public import Theory.SpecificGroups.G2Even.TwoRank.SourceBound
public import Theory.SpecificGroups.G2.MultiplierOrdinary
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient

/-!
# Excluding the G₂ quotient of the tensor point component

For G₂(4), the proved multiplier bound makes the containing center have order
at most two. The original eight-dimensional binary module therefore induces
an elementary automorphism group of rank at least seven, contradicting the
full G₂(4) automorphism rank bound six. For larger even fields the universal
kernel is trivial, contradicting the actual central nonsingular involution.
Every quotient marking and covering projection is retained literally.

Source: Aschbacher--Smith 9.4.1, printed p.735, using I.1.3.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The literal field-four quotient is excluded without a multiplier callback. -/
theorem tensorPoint_containing_not_g2_four (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    {F : Type*} [Field F] [Finite F]
    (a : I ⧸ center I ≃* Atlas.G2.Model F) (hF : Nat.card F = 4) : False := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa [Nat.card_eq_fintype_card] using hF)
  have hZ := ChapterI.LieMultipliers.G2.fourSourceCenter_card_le_two_of_field a hF
  have hlo := m.tensorPoint_containing_automorphism_rank_seven v hv hLI hIN hZ
  have hcover := automorphism_primeRank_le_quotient_center (E := I) 2
  rw [primeRank_equiv 2 (MulAut.congr a)] at hcover
  have hhi := Atlas.G2.EvenTwoRank.source_automorphism_two_rank_le F
    (n := 2) (by decide) hF
  omega

/-- The field-four exclusion applies directly to the source model constructor. -/
theorem tensorPoint_containing_not_g2_four_model (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G)) :
    ¬ ClassificationModels.IsG2At (I ⧸ center I) 4 := by
  rintro ⟨F, hField, hFinite, hF, ⟨a⟩⟩
  exact m.tensorPoint_containing_not_g2_four v hv hLI hIN a hF


/-- All even G₂ rows in the actual Theorem C catalogue are impossible. -/
theorem tensorPoint_containing_not_g2_even (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} [IsQuasisimple I]
    (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    {n : ℕ} (hn : 2 ≤ n) :
    ¬ ClassificationModels.IsG2At (I ⧸ center I) (2 ^ n) := by
  intro hm
  by_cases hn2 : n = 2
  · subst n
    exact m.tensorPoint_containing_not_g2_four_model v hv hLI hIN hm
  · obtain ⟨F, hField, hFinite, hF, ⟨a⟩⟩ := hm
    exact m.tensorPoint_containing_center_ne_bot v hv hLI hIX
      (PerfectCentralCovering.center_eq_bot_of_centralQuotientEquiv
        (Atlas.G2.MultiplierOrdinary.even_universalProjection_ker_eq_bot_of_card_pow
          hF (by omega)) a)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
