module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.Assembly
public import Theory.SpecificGroups.Janko1.Model.InvolutionCentralizer.ProductStructure
public import Theory.SpecificGroups.Janko1.Model.InvolutionCentralizer.Identification
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The J₁ centralizer E-member calculation from its product identification

The actual C₂ × A₅ identification of the standard involution centralizer verifies
all E.1.2(E2) clauses. The radical is a two-group, both residuals agree, and the
radical quotient is its single normal component A₅. Its local tau orbit therefore
generates the layer. The Sylow image has order four, hence is nontrivial and has
full commutator with A₅; its rank is at most two. The conditional theorem
`isEMemberAt_of_equiv` records the structural calculation, while
`isEMemberAt_centralizer` discharges its model-equivalence premise using the
certified matrix centralizer.

The resulting statement has exactly the universal `hmember` type consumed by
`JankoOne.generated_of_centralizer_calculations`; the independent normalizer-
generation calculation remains a separate input to that assembly.

Source: Aschbacher–Smith E.1.2/E.1.5/E.1.14(5), printed pp.209–210, 214,
citing Aschbacher (1982), Lemma 4.9; GLS3, Table 5.3f gives C₂ × A₅.
-/

public section
namespace CFSG.Quasithin.ChapterE.JankoOne.CentralizerMember
open Subgroup Theory.GroupTheory ValuesEvenClassical.RankOneUpper
open Janko1.InvolutionCentralizer

private theorem simple_top_commutator {Q : Type*} [Group Q] [IsSimpleGroup Q]
    [Group.IsPerfect Q] (A : Subgroup Q) (hA : A ≠ ⊥) :
    (⊤ : Subgroup Q) = ⁅(⊤ : Subgroup Q), A⁆ := by
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp h)).elim
  let : (⁅(⊤ : Subgroup Q), A⁆).Normal :=
    normalizer_eq_top_iff.mp (top_unique (normalizer_commutator_ge_left ⊤ A))
  rcases (inferInstance : (⁅(⊤ : Subgroup Q), A⁆).Normal).eq_bot_or_eq_top with h | h
  · exact (hA (le_bot_iff.mp ((commutator_top_left_eq_bot_iff_le_center.mp h).trans hz.le))).elim
  · exact h.symm

/-- Every E.1.2/E.1.5 clause follows from an actual product isomorphism of
the standard involution centralizer. Its construction remains a model calculation. -/
theorem isEMemberAt_of_equiv (e : subgroup ≃* ProductModel)
    (T : Sylow 2 Janko1.Model) (ha : Janko1.a ∈ (T : Subgroup Janko1.Model)) :
    IsEMemberAt 2 (T : Subgroup Janko1.Model) (T : Subgroup Janko1.Model)
      (centralizer ({Janko1.a} : Set Janko1.Model)) := by
  have hTC := sylow_le T ha
  let Q := subgroup ⧸ solvableRadical subgroup
  let eqQ : Q ≃* alternatingGroup (Fin 5) := radicalQuotientEquiv e
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup Q := eqQ.isSimpleGroup
  let : Group.IsPerfect Q := Group.IsPerfect.ofSurjective
    (f := eqQ.symm.toMonoidHom) eqQ.symm.surjective
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp h)).elim
  let : IsQuasisimple Q := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  let : IsQuasisimple (⊤ : Subgroup Q) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have hc : IsComponent Q ⊤ := ⟨.top, inferInstance⟩
  have hl : componentLayer Q = ⊤ := top_unique (le_sSup hc)
  have hclosed : IsTwoClosed (solvableRadical subgroup) := by
    obtain ⟨S, hS⟩ := ((radical_isTwoGroup e).to_subgroup
      (⊤ : Subgroup (solvableRadical subgroup))).exists_le_sylow
    have he : (S : Subgroup (solvableRadical subgroup)) = ⊤ := top_unique hS
    exact ⟨S, he ▸ inferInstance⟩
  let A : Subgroup Q := ((T : Subgroup Janko1.Model).subgroupOf subgroup).map
    (QuotientGroup.mk' (solvableRadical subgroup))
  have hcard : Nat.card A = 4 := sylow_image_card e (T.subtype hTC)
  have hne : A ≠ ⊥ := by
    intro he
    simp only [he, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hT := Janko1.SylowTwo.elementary T
  apply isEMemberAt_of_normal_quotient_component _ _ subgroup hT le_rfl hTC
    ((tau_le _ _).trans hTC) ⟨T.subtype hTC, rfl⟩ hclosed _ (residual_eq e)
    ⊤ hc hl (simple_top_commutator A hne)
  · exact image_rank_le_two T ha
  · rw [hl]
    let : Subsingleton (Q ⧸ (⊤ : Subgroup Q)) := QuotientGroup.subsingleton_quotient_top
    exact ⟨inferInstance, IsPGroup.of_subsingleton 2 _⟩

/-- The standard involution centralizer is an E-member for every Sylow
two-subgroup containing the standard involution. -/
theorem isEMemberAt_centralizer (T : Sylow 2 Janko1.Model)
    (ha : Janko1.a ∈ (T : Subgroup Janko1.Model)) :
    IsEMemberAt 2 (T : Subgroup Janko1.Model) (T : Subgroup Janko1.Model)
      (centralizer ({Janko1.a} : Set Janko1.Model)) := by
  obtain ⟨e⟩ := nonempty_productEquiv
  exact isEMemberAt_of_equiv e T ha

end CFSG.Quasithin.ChapterE.JankoOne.CentralizerMember
