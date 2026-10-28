module
public import Theory.SpecificGroups.SL2.BorelComplementCard
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
/-!
# The full Borel over an even-field rank-one quotient

An odd subgroup of order q−1 normalizing a full Sylow two-subgroup
supplements that Sylow in its relative normalizer. The literal quotient
onto SL₂ identifies the diagonal quotient, and coprimality gives injectivity
on the odd subgroup. Thus any actor preserving the component and Sylow
intersection preserves the Borel, without fixing the chosen supplement.

Source application: Aschbacher–Smith 10.2.3(4), printed p.747.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The original Sylow–Hall join is the whole relative Sylow normalizer. -/
theorem sl2_sylow_odd_borel_eq_normalizer
    (L P D : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hP : IsSylowIn 2 P L) (hDL : D ≤ L) (hD : Nat.card D = Nat.card F - 1)
    (hodd : Odd (Nat.card D)) (hDP : D ≤ normalizer (P : Set G)) :
    P ⊔ D = L ⊓ normalizer (P : Set G) := by
  obtain ⟨Q,hQ⟩ := hP
  have hPL : P ≤ L := hQ ▸ map_subtype_le (Q : Subgroup L)
  have hPsub : P.subgroupOf L = (Q : Subgroup L) := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le hPL,hQ]
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hDN : D.subgroupOf L ≤ normalizer (Q : Set L) := by
    change D.subgroupOf L ≤ normalizer ((Q : Subgroup L) : Set L)
    rw [←hPsub,←subgroupOf_normalizer_eq hPL]
    exact fun _ hx => hDP hx
  have hD' : Nat.card (D.subgroupOf L) = Nat.card F - 1 :=
    (Nat.card_congr (subgroupOfEquivOfLe hDL).toEquiv).trans hD
  have hd : Disjoint (Q : Subgroup L) (D.subgroupOf L) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨m,hm⟩ := Q.isPGroup'.exists_card_eq
    rw [hm,Nat.card_congr (subgroupOfEquivOfLe hDL).toEquiv]
    exact hodd.coprime_two_left.pow_left m
  have he := Matrix.SpecialLinearGroup.sylow_normalizer_complement_of_card q hq Q
    (hk ▸ pCore_isPGroup.le_sylow_of_normal Q) (D.subgroupOf L) hDN hd hD'
  have hm := congrArg (map L.subtype) he
  change ((Q : Subgroup L) ⊔ D.subgroupOf L).map L.subtype =
    (normalizer ((Q : Subgroup L) : Set L)).map L.subtype at hm
  rw [Subgroup.map_sup,hQ,map_subgroupOf_eq_of_le hDL,←hPsub,
    ←subgroupOf_normalizer_eq hPL,subgroupOf_map_subtype,inf_comm] at hm
  exact hm

/-- Component and Sylow invariance imply invariance of the whole literal Borel. -/
theorem sl2_sylow_odd_borel_normalized
    (L S D R : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hP : IsSylowIn 2 (S ⊓ L) L) (hDL : D ≤ L)
    (hD : Nat.card D = Nat.card F - 1) (hodd : Odd (Nat.card D))
    (hDS : D ≤ normalizer (S : Set G))
    (hRL : R ≤ normalizer (L : Set G)) (hRS : R ≤ normalizer (S : Set G)) :
    R ≤ normalizer (((S ⊓ L) ⊔ D : Subgroup G) : Set G) := by
  have hDP : D ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    (le_inf hDS (hDL.trans L.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  rw [sl2_sylow_odd_borel_eq_normalizer L (S ⊓ L) D e hP hDL hD hodd hDP]
  have hRP : R ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    (le_inf hRS hRL).trans inf_normalizer_le_normalizer_inf
  exact (le_inf hRL (hRP.trans (normalizer ((S ⊓ L : Subgroup G) : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf
end CFSG.Quasithin.Chapter1
