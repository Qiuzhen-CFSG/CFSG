module
public import Stellmacher.SectionNine.NineEightTerminalCoatom
public import Theory.GroupAction.InvolutionCentralizingCoatom
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The terminal transvection in the nonreverse branch of (9.8)

If the first-step center is not contained in the terminal module, an actual
first-step module element outside the terminal core has full terminal-module
commutator order two and displacement of order two modulo the terminal center.

The proved (1.2) coatom is centralized by this involution. Involution
rank-nullity bounds its commutator order by two; the exact kernel of the
terminal V/Z action excludes trivial displacement modulo the center.
Thus the full commutator has order two and is disjoint from that center,
and the subgroup product cardinality formula gives quotient index two.

Source: Stellmacher (9.8), printed p.55/PDF p.45, the transvection statement
after the (1.2) fixed-coatom construction.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_eight_terminal_transvection_of_reverse_noncontainment
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hnot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a') :
    ∃ actor : GAt ctx.Γ ctx.criticalPath.a',
      (actor : G) ∈ VAt ctx.Γ ctx.criticalPath.firstStep ∧
      (actor : G) ∉ QAt ctx.Γ ctx.criticalPath.a' ∧
      Nat.card (⁅VAt ctx.Γ ctx.criticalPath.a',Subgroup.zpowers (actor : G)⁆ : Subgroup G) = 2 ∧
      QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a',Subgroup.zpowers (actor : G)⁆ ⊔ ZAt ctx.Γ ctx.criticalPath.a')
        (ZAt ctx.Γ ctx.criticalPath.a') 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let U := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  obtain ⟨fixed,actor,hfixed,hindex,hactor,hactorNot,hcoatomCentral⟩ :=
    nine_eight_terminal_coatom_fixed_actor ctx hb hnot
  let R := ⁅U,Subgroup.zpowers actor⁆
  have hVP := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.2
  have hactorP : actor ∈ GAt Γ cp.a' := hVP hactor
  have hnormal : Subgroup.zpowers actor ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.zpowers_le.mpr hactorP).trans (stabilizer_le_normalizer_v Γ cp.a')
  let _ : IsElementaryAbelian 2 (VAt Γ cp.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).1
  have hinvolution : actor ≠ 1 ∧ actor ^ 2 = 1 :=
    ⟨fun hone => hactorNot (hone ▸ (QAt Γ cp.a').one_mem),
      elemPow_eq_one_of_isElementaryAbelian actor hactor⟩
  let _ : IsElementaryAbelian 2 U :=
    (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.2.1
  have hbound : Nat.card R ≤ 2 := Subgroup.commutator_card_le_two_of_centralizing_index_two
    U fixed actor hinvolution hnormal hfixed hindex hcoatomCentral
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
  refine ⟨⟨actor,hactorP⟩,hactor,hactorNot,hRcard,?_⟩
  change Nat.card (R ⊔ Z : Subgroup G) = 2 * Nat.card Z
  rw [← hcard, Nat.mul_comm]

end Stellmacher.SectionNine
