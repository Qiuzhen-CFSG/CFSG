module
public import Stellmacher.SectionNine.NineTenGeneratingCriticalPair
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Stellmacher.SectionNine.NineThreeSecondExtractionInputs
public import Theory.GroupAction.InvolutionCentralizingCoatom
public import Theory.GroupTheory.NormalizedSupCard
/-!
# The prescribed extracted actor is a first-module transvection

Given the actual index-two intersection of the first module with an extracted
terminal-neighbor stabilizer, every supplied element of that neighbor's center
outside the first core has commutator order two and quotient displacement
order two modulo the first center. The same actor is retained throughout.

The terminal-neighbor center lies in the elementary terminal module and hence
its nonidentity elements are involutions. It normalizes the first module and,
under terminal-center noncontainment, centralizes the displayed coatom.
Involution rank-nullity bounds the commutator order by two. The exact first
quotient-action kernel excludes containment of that commutator in the first
center, giving both its nontriviality and trivial intersection with the center.
The normalized-join cardinality formula gives the required quotient index.

This supplies the prescribed transvection input to (9.4) in the commuting
predecessor case of Stellmacher (9.10), printed p.57/PDF p.47 of
`refs/files/stellmacher-n-group.pdf`. No new actor or reoriented context is
chosen.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_prescribed_actor_first_transvection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (neighbor : ctx.Γ.Vertex)
    (hneighbor : neighbor ∈ Neighborhood ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ neighbor) 2)
    (actor : G) (hactor : actor ∈ ZAt ctx.Γ neighbor)
    (hactorNot : actor ∉ QAt ctx.Γ ctx.criticalPath.firstStep) :
    Nat.card (⁅VAt ctx.Γ ctx.criticalPath.firstStep,Subgroup.zpowers actor⁆ : Subgroup G) = 2 ∧
      QuotientCardEq (⁅VAt ctx.Γ ctx.criticalPath.firstStep,Subgroup.zpowers actor⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.firstStep) (ZAt ctx.Γ ctx.criticalPath.firstStep) 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let U := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let K := U ⊓ GAt Γ neighbor
  let R := ⁅U,Subgroup.zpowers actor⁆
  have hneighborV : ZAt Γ neighbor ≤ VAt Γ cp.a' := by
    rw [VAt,v,Γ.vAt_def]
    exact le_sSup ⟨neighbor,hneighbor,rfl⟩
  have hneighborP : ZAt Γ neighbor ≤ GAt Γ cp.firstStep :=
    hneighborV.trans (lemma_seven_four ctx.sectionSeven Γ cp).reverse_containment.2
  have hactorP : actor∈GAt Γ cp.firstStep := hneighborP hactor
  have hcyclic : Subgroup.zpowers actor ≤ ZAt Γ neighbor := Subgroup.zpowers_le.mpr hactor
  have hnormal : Subgroup.zpowers actor ≤ Subgroup.normalizer (U : Set G) :=
    (hcyclic.trans hneighborP).trans (stabilizer_le_normalizer_v Γ cp.firstStep)
  let _ : IsElementaryAbelian 2 (VAt Γ cp.a') :=
    (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.2.1
  have hinvolution : actor ≠ 1 ∧ actor ^ 2 = 1 :=
    ⟨fun hone => hactorNot (hone ▸ (QAt Γ cp.firstStep).one_mem),
      elemPow_eq_one_of_isElementaryAbelian actor (hneighborV hactor)⟩
  let _ : IsElementaryAbelian 2 U :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).1
  have hcoatomCentral : K ≤ Subgroup.centralizer (Subgroup.zpowers actor : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (nine_ten_terminal_neighbor_center_centralizes_first_coatom ctx hb hterminalNot
        neighbor hneighbor)).trans (Subgroup.centralizer_le hcyclic)
  have hbound : Nat.card R ≤ 2 := Subgroup.commutator_card_le_two_of_centralizing_index_two
    U K actor hinvolution hnormal inf_le_left hindex hcoatomCentral
  obtain ⟨_,hmoduleCore,hkernel⟩ := nine_next_center_commutator_and_kernel
    ctx hb cp.firstStep ⟨1,Γ.act_one _⟩
  have hRnot : ¬ R ≤ Z := fun hle => hactorNot ((hkernel actor hactorP).mp hle)
  have hRne : R ≠ ⊥ := fun heq => hRnot (heq ▸ bot_le)
  have hRcard : Nat.card R = 2 := by
    have hpos := (Subgroup.one_lt_card_iff_ne_bot R).mpr hRne
    omega
  have hRZ : R ⊓ Z = ⊥ := by
    by_contra hne
    have hpos := (Subgroup.one_lt_card_iff_ne_bot (R ⊓ Z)).mpr hne
    have heq : R ⊓ Z = R := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    exact hRnot (heq ▸ inf_le_right)
  have hRU : R ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp hnormal
  have hQP : QAt Γ cp.firstStep ≤ GAt Γ cp.firstStep := by
    rw [QAt,q,Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hZU : Z ≤ U := by
    change ZAt ctx.Γ cp.firstStep ≤ U
    rw [← hmoduleCore]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hQP.trans (stabilizer_le_normalizer_v Γ cp.firstStep))
  have hab : U ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hnormalize : R ≤ Subgroup.normalizer (Z : Set G) :=
    hRU.trans (hab.trans ((Subgroup.centralizer_le hZU).trans
      (Subgroup.centralizer_le_normalizer _)))
  have hcard := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes Z R hnormalize
  rw [inf_comm,hRZ,Subgroup.card_bot,hRcard,one_mul,sup_comm] at hcard
  refine ⟨hRcard,?_⟩
  change Nat.card (R ⊔ Z : Subgroup G) = 2 * Nat.card Z
  rw [← hcard,Nat.mul_comm]

end Stellmacher.SectionNine
