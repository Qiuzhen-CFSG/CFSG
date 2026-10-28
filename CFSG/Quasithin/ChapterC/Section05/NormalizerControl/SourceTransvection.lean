module
public import Theory.Representation.CentralizerQuotientAction
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.CubicAction
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CubicCentralizer

/-!
# The original A₃ pair acts by transvections on the C.5.13 span

The C.5.6 commutator and fixed-subgroup equalities show that U₁ˣ acts on
every normalized elementary span V₁ containing U₁ with displacement
U₁∩U₁ˣ. For an actual A₃ block U₁ has order four, so this proper nontrivial
intersection has order two. Literal conjugation on V₁ therefore induces
transvections. The relative theorem retains x in the ambient group and
constructs the action inside X₁, where U₁ˣ lies. No action model or assumed
transvection remains in this step. Combining with the cubic-normality
argument gives normality of U₁ when the remaining earlier order-two Sylow
and inverted cubic hypotheses are supplied.

Source: Aschbacher–Smith, C.5.6(2) and C.5.13, printed pp.156,162.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The C.5.6 pair supplies the precise commutator and fixed subgroup on
any elementary normal V₁ containing U₁ and normalizing U₁ˣ. -/
theorem pair_displacement_on_span
    (U B E V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hUV : U ≤ V) (hVB : V ≤ normalizer (B : Set G))
    (hpair : ⁅B,U⁆ = E) (hfixed : B ⊓ centralizer (U : Set G) = E) :
    ⁅B,V⁆ = E ∧ B ⊓ centralizer (V : Set G) = E ∧ B ⊓ V = E := by
  have hVCU : V ≤ centralizer (U : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hUV)
  have hEV : E ≤ V := hpair.symm.trans_le
    ((commutator_mono le_rfl hUV).trans (commutator_le_right _ _))
  have hEB : E ≤ B := hfixed.symm.trans_le inf_le_left
  have hBV : B ⊓ V = E := le_antisymm
    ((inf_le_inf_left _ hVCU).trans_eq hfixed) (le_inf hEB hEV)
  have hcomm : ⁅B,V⁆ = E := by
    apply le_antisymm
    · exact (le_inf (le_normalizer_iff_commutator_le_left.mp hVB)
        (commutator_le_right _ _)).trans_eq hBV
    · exact hpair.symm.trans_le (commutator_mono le_rfl hUV)
  refine ⟨hcomm,?_,hBV⟩
  apply le_antisymm ((inf_le_inf_left _ (centralizer_le hUV)).trans_eq hfixed)
  exact le_inf hEB (hEV.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance))

/-- In the A₃ case the source commutator E₁ has order two. Every element
of U₁ˣ therefore induces a transvection in the literal faithful quotient. -/
theorem pair_transvections_on_span
    (U B E V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hUV : U ≤ V) (hVB : V ≤ normalizer (B : Set G))
    (hpair : ⁅B,U⁆ = E) (hfixed : B ⊓ centralizer (U : Set G) = E)
    (hE : Nat.card E ≤ 2) (b : G) (hb : b ∈ B) :
    LinearMap.GeneralLinearGroup.toLinearEquiv
      ((Representation.centralizerQuotient V).asGroupHom
        (QuotientGroup.mk' (centralizer (V : Set G)) b)) ∈
          LinearEquiv.transvections (ZMod 2) (Additive V) := by
  apply Representation.centralizerQuotient_transvection_of_commutator_card V b E hE
  intro v hv
  rw [← (pair_displacement_on_span U B E V hUV hVB hpair hfixed).1]
  exact commutator_mem_commutator hb hv

/-- C.5.13's A₃ normalizer bound with the quotient action and its
transvection constructed from the original pair's order-two commutator. -/
theorem cubic_pair_module_normal
    (V K U B E : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hshort : CFSG.Quasithin.ChapterC.IsShort K)
    (hU : U = ConjugateSource.RankOne.U K) (hUV : U ≤ V)
    (hVN : V ≤ normalizer (K : Set G))
    (hVB : V ≤ normalizer (B : Set G))
    (hpair : ⁅B,U⁆ = E) (hfixed : B ⊓ centralizer (U : Set G) = E)
    (hE : Nat.card E ≤ 2)
    (Tstar : Sylow 2 (G ⧸ centralizer (V : Set G))) (hT : Nat.card Tstar = 2)
    (hK : Nat.card (K.map (QuotientGroup.mk' (centralizer (V : Set G)))) = 3)
    (b : G) (hb : b ∈ B) (hbi : IsInvolution (QuotientGroup.mk' (centralizer (V : Set G)) b))
    (hinvert : ∀ c ∈ K.map (QuotientGroup.mk' (centralizer (V : Set G))),
      QuotientGroup.mk' (centralizer (V : Set G)) b * c *
        (QuotientGroup.mk' (centralizer (V : Set G)) b)⁻¹ = c⁻¹) : U.Normal := by
  have ht := pair_transvections_on_span U B E V hUV hVB hpair hfixed hE b hb
  have hVC : V ≤ centralizer (U : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hUV)
  subst U
  exact cubic_block_module_normal V K hshort hUV hVN hVC
    (Representation.centralizerQuotient V) (Representation.centralizerQuotient_faithful V)
    Tstar hT hK b hbi hinvert ht
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl

namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G}

/-- The actual A₃ module has four elements and its noncommuting conjugate
meets it in precisely two elements, including no central covering layer. -/
theorem alternating_three_pair_card
    {F : Type*} [Field F] (h : Setup R K F) (ha : ChapterC.IsAlternatingBlock K 3)
    {x : G} (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    Nat.card (U K ⊓ (U K).map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) = 2 := by
  let B := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  let E := U K ⊓ B
  have hcU := h.cubic_module_card ha
  have hcB : Nat.card B = Nat.card (U K) := card_map_of_injective (MulAut.conj x⁻¹).injective
  have hne : E ≠ ⊥ := by
    intro hz
    exact hnc (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      ((h.commutator_eq_fixed hx hnc).2.trans hz)))
  have hlt : E < U K := lt_of_le_of_ne inf_le_left (by
    intro he
    have hUB : U K ≤ B := he.symm.trans_le inf_le_right
    have heB : U K = B := eq_of_le_of_card_ge hUB hcB.le
    let := h.elementary
    apply hnc
    change B ≤ centralizer (U K : Set G)
    rw [← heB]
    exact le_centralizer _)
  have hcardle : Nat.card E ≤ Nat.card (U K) :=
    Nat.card_le_card_of_injective (inclusion (show E ≤ U K from inf_le_left)) (inclusion_injective _)
  have hcardne : Nat.card E ≠ Nat.card (U K) := fun he =>
    hlt.ne (eq_of_le_of_card_ge inf_le_left he.ge)
  have hcardlt : Nat.card E < 4 := (lt_of_le_of_ne hcardle hcardne).trans_eq hcU
  have hcardpos : 1 < Nat.card E := by
    have hp : 0 < Nat.card E := Nat.card_pos
    have hnot : Nat.card E ≠ 1 := fun he => hne ((card_eq_one).mp he)
    omega
  have hd : Nat.card E ∣ 4 := hcU ▸ card_dvd_of_le (show E ≤ U K from inf_le_left)
  rcases (by omega : Nat.card E = 2 ∨ Nat.card E = 3) with hh | hh
  · exact hh
  · rw [hh] at hd
    norm_num at hd
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl



namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G}
/-- The source actor x remains in the ambient group: only its module
U₁ˣ lies in X₁. The canonical quotient action is constructed inside X₁. -/
theorem alternating_three_relative_transvections
    {F : Type*} [Field F] (h : Setup R K F) (ha : ChapterC.IsAlternatingBlock K 3)
    {x : G} (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (X₁ V₁ : Subgroup G) [IsElementaryAbelian 2 V₁]
    (hVX : V₁ ≤ X₁) (hXV : X₁ ≤ normalizer (V₁ : Set G))
    (hUV : U K ≤ V₁)
    (hVN : V₁ ≤ normalizer ((U K).map (MulAut.conj x⁻¹).toMonoidHom : Set G))
    (hBX : (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ X₁) :
    let : (V₁.subgroupOf X₁).Normal := normal_subgroupOf_iff_le_normalizer hVX |>.mpr hXV
    let : IsElementaryAbelian 2 (V₁.subgroupOf X₁) := IsElementaryAbelian.subgroupOf hVX
    ∀ b (hb : b ∈ (U K).map (MulAut.conj x⁻¹).toMonoidHom),
    LinearMap.GeneralLinearGroup.toLinearEquiv
      ((Representation.centralizerQuotient (V₁.subgroupOf X₁)).asGroupHom
        (QuotientGroup.mk' (centralizer (V₁.subgroupOf X₁ : Set X₁)) ⟨b,hBX hb⟩)) ∈
          LinearEquiv.transvections (ZMod 2) (Additive (V₁.subgroupOf X₁)) := by
  let : (V₁.subgroupOf X₁).Normal := (normal_subgroupOf_iff_le_normalizer hVX).mpr hXV
  let : IsElementaryAbelian 2 (V₁.subgroupOf X₁) := IsElementaryAbelian.subgroupOf hVX
  dsimp only
  intro b hb
  let B := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  let E := U K ⊓ B
  have hEB : E ≤ X₁ := inf_le_right.trans hBX
  apply Representation.centralizerQuotient_transvection_of_commutator_card
    (V₁.subgroupOf X₁) ⟨b,hBX hb⟩ (E.subgroupOf X₁)
  · rw [Nat.card_congr (subgroupOfEquivOfLe hEB).toEquiv]
    exact (alternating_three_pair_card h ha hx hnc).le
  · intro v hv
    have hcomm : ⁅B,V₁⁆ ≤ E := by
      apply le_trans (le_inf (le_normalizer_iff_commutator_le_left.mp hVN)
        (le_normalizer_iff_commutator_le_right.mp (hBX.trans hXV)))
      have hVC : V₁ ≤ centralizer (U K : Set G) :=
        (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hUV)
      exact (inf_le_inf_left _ hVC).trans_eq (h.conjugate_fixed_intersection hx hnc)
    exact hcomm (commutator_mem_commutator hb hv)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
