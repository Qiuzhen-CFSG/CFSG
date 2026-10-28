module
public import Stellmacher.SectionNine.NineTenTransvectionCentralizingNeighbor
public import Stellmacher.SectionNine.NineTenCenterCommutatorCyclic
public import Stellmacher.SectionNine.LemmaNineNine

/-!
# A centralizing neighbor mover for the literal center commutator in (9.10)

Retain one actual critical path of length greater than three, its terminal
order-thirty-two wreath classification and order-eight backward intersection,
and the terminal/initial-stabilizer coatom supplied by its own extraction.
An element of the penultimate stabilizer centralizes the literal source
R=[Z_initial,V_terminal] and carries the terminal vertex to the backward one.

Actual (9.9) excludes first-center containment. Criticality chooses an
initial-center actor outside the terminal core, and the retained coatom gives
its order-two full displacement and transvection quotient. The independent
center/cyclic identity identifies that displacement with the entire source R.
The retained-actor centralizing-neighbor theorem then supplies the required
mover with the original ambient action and path offsets.

This proves the assertion immediately following Stellmacher (9.10)(6),
printed p.58 of `refs/files/stellmacher-n-group.pdf`. The coatom belongs to
this same path: no coatom from another orientation is inherited.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_center_commutator_centralizing_neighbor
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hUcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (hIcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) = 2^3)
    (hcoatom : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.a')
      (VAt ctx.Γ ctx.criticalPath.a' ⊓ GAt ctx.Γ ctx.criticalPath.a) 2) :
    ∃ y : G,
      y ∈ GAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ∧
      y ∈ Subgroup.centralizer
        ((⁅ZAt ctx.Γ ctx.criticalPath.a,VAt ctx.Γ ctx.criticalPath.a'⁆ : Subgroup G) : Set G) ∧
      ctx.Γ.act y ctx.criticalPath.a' = ctx.criticalPath.path
        ⟨ctx.criticalPath.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
  have hshort : 1 < ctx.criticalPath.length := by omega
  have hfirstNot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a' := by
    intro hcontain
    have := lemma_nine_nine_ambient ctx hcontain
    omega
  obtain ⟨actor,hactor,hactorNot⟩ := SetLike.not_le_iff_exists.mp ctx.criticalPath.critical.2
  have hfirst := (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment
  have hactorP : actor ∈ GAt ctx.Γ ctx.criticalPath.a' := hfirst.2 (hfirst.1 hactor)
  obtain ⟨hcard,hindex⟩ := nine_ten_transvection_of_coatom ctx hshort hfirstNot hcoatom
    actor hactor hactorNot
  have heq := nine_ten_initial_center_commutator_eq_cyclic ctx hshort actor hactor hactorNot
  obtain ⟨y,hyP,hyR,hmove⟩ := nine_ten_transvection_centralizing_neighbor ctx hb
    hUcard hmodel hIcard ⟨actor,hactorP⟩ (hfirst.1 hactor) hcard hindex
  exact ⟨y,hyP,heq.symm ▸ hyR,hmove⟩

end Stellmacher.SectionNine
