module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MixedZeroCore.Assembly
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLine
public import Theory.GroupTheory.CubicPairFactor

/-!
# The mixed cubic factor from the original Cartan quotient

If the old residual moves the original tensor line, T acts nontrivially
on that line: otherwise the line belongs to Ω₁Z(T), which the residual
centralizes. Mark the Cartan quotient inside S₃ × S₃ by its sum and
difference cubic characters. The tensor-factor exchange distinguishes
the two signs. The elementary two-group calculation then constructs
the field--swap image, odd on the line character and trivial on B.

Lifting the first symmetric factor constructs a subgroup of the original
A∨T, normalized by T and B, which supplements B on A and has actual
O₂ quotient S₃. This is precisely the input to MixedZeroCore.Local.

Construction of the marked quotient remains explicit in
MixedCartanPairInput. Thus the final theorem is conditional assembly;
it does not claim the original source construction has been completed.
The cubic-factor task retains final discharge of this input.

Source: Aschbacher–Smith, original 9.3.1, printed p.732 of
refs/quasithin.pdf, the third reduction and construction of Dσ T₂.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 Chapter4 ChapterE MixedZeroCore
open ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- If the old residual moves the original line, the full Sylow acts
nontrivially on that same line. This is the fixed-center part of the third
reduction in original 9.3.1. -/
theorem sylow_moves_tensorLine_of_old_residual_moves
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G)) :
    ¬ (T : Subgroup G) ≤ centralizer (m.tensorLine : Set G) := by
  intro hT
  have hline : m.tensorLine ≤ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
    let := m.tensorLine_elementary
    intro u hu
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    exact ⟨m.tensorLine_le_sylow hu, elemPow_eq_one_of_isElementaryAbelian u hu,
      fun t ht => (hT ht u hu).symm⟩
  exact hmove ((m.old_residual_centralizes_sylowOmega hH).trans (centralizer_le hline))

/-- The actual Cartan quotient marked by its two cubic characters.
The first character is its action on the original tensor line. The product
of the signs detects exchange of the original tensor factors. No symmetric
factor, field--swap element, or desired subgroup U is part of this input. -/
structure CartanPairMarking (A B : Subgroup G) where
  quotient : (A ⊔ (T : Subgroup G) : Subgroup G) →*
    (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
  kernel_eq : quotient.ker = pCore 2 (A ⊔ (T : Subgroup G) : Subgroup G)
  cartan_image : (A.subgroupOf (A ⊔ (T : Subgroup G))).map quotient =
    (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))
  hall_image : (B.subgroupOf (A ⊔ (T : Subgroup G))).map quotient =
    (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3))
  line_kernel (x : (A ⊔ (T : Subgroup G) : Subgroup G)) :
    (quotient x).1 = 1 ↔ (x : G) ∈ centralizer (m.tensorLine : Set G)
  exchange_sign (t : T) (ht : (t : G) ∉ normalizer (L : Set G)) :
    Equiv.Perm.sign (quotient (inclusion le_sup_right t)).1 ≠
      Equiv.Perm.sign (quotient (inclusion le_sup_right t)).2

/-- Construct the field--swap image from the original moving line and an
actual marked quotient. Both characters and the original Sylow are retained. -/
theorem exists_field_swap_of_cartanPairMarking
    {H A B : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (c : m.CartanPairMarking A B)
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G)) :
    ∃ t : T,
      (c.quotient (inclusion le_sup_right t)).1 ∉ alternatingGroup (Fin 3) ∧
      (c.quotient (inclusion le_sup_right t)).2 = 1 := by
  let f := c.quotient.comp (inclusion (show (T : Subgroup G) ≤ A ⊔ (T : Subgroup G) from le_sup_right))
  apply CubicPairFactor.exists_first_odd_second_one T.isPGroup' f
  · obtain ⟨t,ht,htc⟩ := Set.not_subset.mp
      (m.sylow_moves_tensorLine_of_old_residual_moves hH hmove)
    refine ⟨⟨t,ht⟩,?_⟩
    exact fun he => htc ((c.line_kernel (inclusion le_sup_right ⟨t,ht⟩)).mp he)
  · obtain ⟨t,ht,htn⟩ := Set.not_subset.mp m.sylow_not_normalizes_component
    exact ⟨⟨t,ht⟩,c.exchange_sign ⟨t,ht⟩ htn⟩

/-- The literal U obtained by lifting the first symmetric factor satisfies
all clauses used by the corrected F.1.1 consumer. The marked quotient is
still an explicit source input. -/
theorem cubicFactor_of_cartanPairMarking
    {H A B : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hBA : B ≤ A) (c : m.CartanPairMarking A B)
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G)) :
    ∃ U : Subgroup G, CubicFactor T A B U := by
  obtain ⟨t,ht1,ht2⟩ := m.exists_field_swap_of_cartanPairMarking hH c hmove
  obtain ⟨U,hUP,hPN,hcover,he⟩ := CubicPairFactor.exists_normal_factor
    (A ⊔ (T : Subgroup G)) A B le_sup_left
    c.quotient (c.kernel_eq ▸ pCore_isPGroup) c.cartan_image c.hall_image
    (inclusion le_sup_right t) ht1 ht2
  exact ⟨U,hUP,(show (T : Subgroup G) ≤ A ⊔ (T : Subgroup G) from le_sup_right).trans hPN,
    (hBA.trans le_sup_left).trans hPN,hcover,he⟩

/-- The remaining original-source construction of the marked Cartan quotient.
The entire original contract is retained so a source producer may use any
of its ambient hypotheses. -/
@[expose] def MixedCartanPairInput : Prop :=
  ∀ (H : Subgroup G), H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal →
    1 < generationParameter H →
    (((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5)) →
    ∀ (A B : Subgroup G), A ≤ sourceOrbitBorel T L →
      Nat.card A = 9 → IsElementaryAbelian 3 A →
      B ≤ A → B ≤ (pResidual 2 H).map H.subtype → Nat.card B = 3 →
      IsHallSubgroup oddPrimes (B.subgroupOf (H ⊓ D.maximalLocal)) →
      B = A ⊓ centralizer (m.tensorLine : Set G) →
      pCore 2 (H ⊔ A : Subgroup G) = ⊥ →
      ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G) →
      Nonempty (m.CartanPairMarking A B)

/-- Conditional assembly into the parent's exact cubic-factor contract.
Completion of the source requires constructing MixedCartanPairInput. -/
theorem mixedCubicFactorInput_of_cartanPairInput
    (pair : m.MixedCartanPairInput) : m.MixedCubicFactorInput := by
  intro H hH hlarge eK A B hAB hA9 hAe hBA hBK hB3 hHall hBC hzero hmove
  obtain ⟨c⟩ := pair H hH hlarge eK A B hAB hA9 hAe hBA hBK hB3 hHall hBC hzero hmove
  exact m.cubicFactor_of_cartanPairMarking hH hBA c hmove

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
