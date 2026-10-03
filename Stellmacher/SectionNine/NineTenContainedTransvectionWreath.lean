module

public import Stellmacher.SectionNine.LemmaNineFive
public import Stellmacher.SectionNine.LemmaNineSeven
public import Stellmacher.SectionNine.NineSixSmallModule
public import Stellmacher.SectionNine.NineTenTransvectionCoatom
public import Stellmacher.SectionNine.NineTenNormalizedExtraction

/-!
# Only the wreath transvection case survives at long critical distance

Assume the exact actor, index-two displacement, and backward containment
hypotheses of (9.5), now at critical distance greater than three. The terminal
module has order thirty-two, its core quotient is SL₂(2) wreath C₂, and its
intersection with the prescribed backward module has order eight.

Apply the proved ambient (9.5) dichotomy. If the terminal module has order
eight, endpoint alignment gives the same order for the first-step module.
The actual small-module proof of (9.6) gives index two for its intersection
with the third module. The proved ambient (9.7) then forces critical length
three, a contradiction. No unfinished case of (9.6) is used.

This is the model and cardinality implication in Stellmacher (9.10)(6),
printed p.58. The source's earlier choice or reorientation that supplies
the backward commutator containment remains a separate prerequisite; this
result retains that literal input and the supplied transvection actor.
The center-commutator corollary uses the same second extraction to provide
its index-two coatom, then takes an initial-center element outside the
terminal core. Its cyclic commutator lies in the supplied full center
commutator, so the same classification follows without an extra index
hypothesis.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_wreath_of_transvection_containment
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (aMinus2 : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) aMinus2)
    (t : G)
    (ht : t ∈ VAt ctx.Γ ctx.criticalPath.firstStep ∧
      t ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers t⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a')
      (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hcontain : ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers t⁆ ≤
      VAt ctx.Γ aMinus2) :
      (Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 5 ∧
        QuotientIsModel
          (GAt ctx.Γ ctx.criticalPath.a')
          (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2 ∧
        Nat.card
          (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ aMinus2 : Subgroup G) = 2 ^ 3) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 3 < cp.length := hb
  have hshort : 1 < cp.length := by omega
  rcases lemma_nine_five_ambient ctx hshort aMinus2 hpath t ht hindex hcontain with
    ⟨hsmall, _⟩ | hlarge
  · exfalso
    obtain ⟨mover, _, hmove⟩ := lemma_seven_five_endpoint_alignment
      ctx.sectionSeven Γ cp ctx.commutator_eq
    have hfirstCard : Nat.card (VAt Γ cp.firstStep) ≤ 8 := by
      change Nat.card (VAt Γ cp.a') = 2 ^ 3 at hsmall
      change Nat.card (v Γ cp.firstStep) ≤ 8
      rw [← hmove, VAt, v_act,
        Subgroup.card_map_of_injective (MulAut.conj mover⁻¹).injective] at hsmall
      exact hsmall.le
    let third := cp.path ⟨3, by omega⟩
    have hthird : IsCriticalPathOffset Γ cp 3 third := ⟨⟨3, by omega⟩, rfl, rfl⟩
    have hfour := (lemma_nine_three_ambient ctx hshort cp.a ⟨1, Γ.act_one _⟩).2
    have hcoatom := nine_six_ambient_of_small_module ctx third hthird hfour hfirstCard
    have hthree := (lemma_nine_seven_ambient ctx hshort third hthird hcoatom).1
    omega
  · exact hlarge

/-- The same retained extraction supplies the transvection input from its actual coatom. -/
public theorem nine_ten_wreath_of_center_commutator_containment
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hfirstNot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a')
    (second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep second
      (VAt ctx.Γ ctx.criticalPath.a') E A0 actor)
    (hnew : ctx.Γ.act data.x⁻¹ second = ctx.criticalPath.a)
    (hcontain : ⁅ZAt ctx.Γ ctx.criticalPath.a, VAt ctx.Γ ctx.criticalPath.a'⁆ ≤
      VAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) :
    Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 5 ∧
      QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
        (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2 ∧
      Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) = 2 ^ 3 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hcoatom : QuotientCardEq (VAt Γ cp.a') (VAt Γ cp.a' ⊓ GAt Γ cp.a) 2 := by
    change Nat.card (VAt Γ cp.a') = 2 * Nat.card (VAt Γ cp.a' ⊓ GAt Γ cp.a : Subgroup G)
    rw [← hnew, ← data.coatom_eq]
    exact data.coatom_card
  obtain ⟨t, ht, hnot⟩ := Set.not_subset.mp cp.critical.2
  have hdisplacement := (nine_ten_transvection_of_coatom ctx hshort hfirstNot
    hcoatom t ht hnot).2
  have htFirst := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1 ht
  have hR : ⁅VAt Γ cp.a', Subgroup.zpowers t⁆ ≤ ⁅ZAt Γ cp.a, VAt Γ cp.a'⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mono (Subgroup.zpowers_le.mpr ht) le_rfl
  exact nine_ten_wreath_of_transvection_containment ctx hb _
    ⟨⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩, rfl, rfl⟩
    t ⟨htFirst, hnot⟩ hdisplacement (hR.trans hcontain)

end Stellmacher.SectionNine
