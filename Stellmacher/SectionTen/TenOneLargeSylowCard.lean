module
public import Stellmacher.SectionTen.TenOneLargeFirstFrobenius

/-!
# Exact Sylow cardinality in the large terminal case

The distinguished graph Sylow has order four times that of the first
vertex core. Its image under the actual Frobenius20 quotient has order
four, and the canonical quotient kernel is the first core. The original
edge Sylow data and subgroup index multiplication give the equality.

This exposes the calculation needed both for the large Sylow bounds and
for recognizing an ambient involution-centralizer core when the prescribed
Sylow has order2048. No replacement Sylow or cardinal assumption is used.
Source: Stellmacher (10.1)(19) and its final Sylow bound, printed p65.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_large_sylow_card
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    : Nat.card T = 4 * Nat.card (QAt ctx.Γ ctx.criticalPath.firstStep) := by
  let P := GAt ctx.Γ ctx.criticalPath.firstStep
  let Q := QAt ctx.Γ ctx.criticalPath.firstStep
  obtain ⟨φ,_hfaithful,projection,hsurj,hker⟩:=ten_one_large_first_frobenius ctx middle hpath hno
  let model:=SemidirectProduct C5 C4 φ
  obtain ⟨_,sylow,hsylow⟩:=(SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  let image : Sylow 2 model:=sylow.mapSurjective hsurj
  have hmodelCard : Nat.card model=20:=by
    rw [SemidirectProduct.card]
    simp [C5,C4]
  let _ : Finite model:=Nat.finite_of_card_ne_zero (by rw [hmodelCard];decide)
  have himageCard : Nat.card image=4:=by
    rw [image.card_eq_multiplicity,hmodelCard]
    rw [show 20=2^2*5 from rfl,
      Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow,
      Nat.prime_two.factorization,(show Nat.Prime 5 from by decide).factorization]
    norm_num
  have hQP : Q≤P:=by
    change ctx.Γ.twoCoreAt _≤P
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hQT : Q≤T:=(local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  have hratio : Q.relIndex T=4:=by
    have hh:=Subgroup.relIndex_ker (sylow:Subgroup P) projection
    rw [hker] at hh
    have hmap:=Subgroup.relIndex_map_map_of_injective (Q.subgroupOf P)
      (sylow:Subgroup P) P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hQP,hsylow] at hmap
    exact hmap.trans (hh.trans himageCard)
  have hh:=(Q.subgroupOf T).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQT).toEquiv] at hh
  change Q.relIndex T*Nat.card Q=Nat.card T at hh
  rw [hratio] at hh
  exact hh.symm

end Stellmacher.SectionTen
