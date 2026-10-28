module

public import Stellmacher.SectionNine.NineTenCoatomCentralization
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Stellmacher.SectionNine.NineThreeSecondExtractionInputs
public import Theory.GroupAction.InvolutionCentralizingCoatom
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The actual coatom gives a transvection in (9.10)

Assume the terminal-module intersection with the initial stabilizer has
index two, as furnished by the normalized second geometric extraction.
If the first-step center is not contained in the terminal module, every
initial-center element outside the terminal core has full commutator order
two and nontrivial displacement of order two modulo the terminal center.

The proved coatom-centralization theorem fixes that index-two subgroup.
The initial-center element is an involution and normalizes the elementary
terminal module; involution rank-nullity bounds its commutator by two.
The proved kernel criterion on the literal terminal quotient excludes
containment of that commutator in the terminal center. Its order is thus
exactly two, its intersection with the center is trivial, and the normalized
join cardinality formula gives the exact quotient index.

Source: Stellmacher (9.10)(2), printed p.57 of
`refs/files/stellmacher-n-group.pdf`. The coatom index and the source
center noncontainment remain explicit inputs from the actual extraction;
no transvection assertion is assumed.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_transvection_of_coatom
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hnot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.a')
      (VAt ctx.Γ ctx.criticalPath.a' ⊓ GAt ctx.Γ ctx.criticalPath.a) 2)
    (actor : G)
    (hactor : actor ∈ ZAt ctx.Γ ctx.criticalPath.a)
    (hactorNot : actor ∉ QAt ctx.Γ ctx.criticalPath.a') :
    Nat.card (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ : Subgroup G) = 2 ∧
      QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let U := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let K := U ⊓ GAt Γ cp.a
  let R := ⁅U, Subgroup.zpowers actor⁆
  have hcontain := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment
  have hactorP : actor ∈ GAt Γ cp.a' := hcontain.2 (hcontain.1 hactor)
  have hcyclic : Subgroup.zpowers actor ≤ ZAt Γ cp.a := Subgroup.zpowers_le.mpr hactor
  have hnormal : Subgroup.zpowers actor ≤ Subgroup.normalizer (U : Set G) :=
    (hcyclic.trans (hcontain.1.trans hcontain.2)).trans
      (stabilizer_le_normalizer_v Γ cp.a')
  let _ : IsElementaryAbelian 2 (VAt Γ cp.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).1
  have hinvolution : actor ≠ 1 ∧ actor ^ 2 = 1 :=
    ⟨fun hone => hactorNot (hone ▸ (QAt Γ cp.a').one_mem),
      elemPow_eq_one_of_isElementaryAbelian actor (hcontain.1 hactor)⟩
  let _ : IsElementaryAbelian 2 U :=
    (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.2.1
  have hcoatomCentral : K ≤ Subgroup.centralizer (Subgroup.zpowers actor : Set G) := by
    have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (nine_ten_initial_center_centralizes_terminal_coatom ctx hb hnot)
    exact (Subgroup.le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le hcyclic)
  have hbound : Nat.card R ≤ 2 := Subgroup.commutator_card_le_two_of_centralizing_index_two
    U K actor hinvolution hnormal inf_le_left hindex hcoatomCentral
  obtain ⟨alignment, _, halign⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have horbit : IsConjugateVertex Γ cp.firstStep cp.a' := ⟨alignment, halign⟩
  obtain ⟨hZcard, hmoduleCore, hkernel⟩ :=
    nine_next_center_commutator_and_kernel ctx hb cp.a' horbit
  have hRnot : ¬ R ≤ Z := fun hle => hactorNot ((hkernel actor hactorP).mp hle)
  have hRne : R ≠ ⊥ := fun heq => hRnot (heq ▸ bot_le)
  have hRcard : Nat.card R = 2 := by
    have hpos := (Subgroup.one_lt_card_iff_ne_bot R).mpr hRne
    omega
  have hRZ : R ⊓ Z = ⊥ := by
    by_contra hne
    have hpos := (Subgroup.one_lt_card_iff_ne_bot (R ⊓ Z)).mpr hne
    have hequal : R ⊓ Z = R := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    exact hRnot (hequal ▸ inf_le_right)
  have hRU : R ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp hnormal
  have hQP : QAt Γ cp.a' ≤ GAt Γ cp.a' := by
    rw [QAt, q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hZU : Z ≤ U := by
    change ZAt ctx.Γ cp.a' ≤ U
    rw [← hmoduleCore]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hQP.trans (stabilizer_le_normalizer_v Γ cp.a'))
  have hab : U ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hnormalize : R ≤ Subgroup.normalizer (Z : Set G) :=
    hRU.trans (hab.trans ((Subgroup.centralizer_le hZU).trans
      (Subgroup.centralizer_le_normalizer _)))
  have hcard := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes Z R hnormalize
  rw [inf_comm, hRZ, Subgroup.card_bot, hRcard, one_mul, sup_comm] at hcard
  refine ⟨hRcard, ?_⟩
  change Nat.card (R ⊔ Z : Subgroup G) = 2 * Nat.card Z
  rw [← hcard, Nat.mul_comm]

end Stellmacher.SectionNine
