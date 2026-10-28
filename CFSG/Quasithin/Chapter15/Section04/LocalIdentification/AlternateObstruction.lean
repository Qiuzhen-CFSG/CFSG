module

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.Residual
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.RankObstruction

/-!
# The alternate-amalgam obstruction in the concrete configuration

The cross-commutator bound puts `I′` in `N_G(O₂(Xᵢ))`. An E₉ in `I′`
disjoint from `Xᵢ` centralizes its cyclic order-three quotient. Restricting all
subgroups to this actual normalizer supplies the relative normality and
coprime kernel required for the rank calculation.

Thus the SQTK three-rank bound rules out this pair of hypotheses. The source
15.4.21–22 classification must still construct the E₉ and the cross-commutator
bound before the conditional generalized-Fitting conclusion applies.

Source: Aschbacher–Smith, Lemma 15.4.23, printed p.1165. This proof uses the
normalizer of `O₂(Xᵢ)`, whose containment follows explicitly from the bound;
it does not assume the source's unstated containment in `N_G(I)`.
-/

namespace CFSG.Quasithin.Chapter15.Section04.Source
open Subgroup
variable {G : Type*} [Group G] [Finite G] {d : Geometry G}

/-- The elementary rank contradiction from explicit alternate-amalgam data. -/
public theorem LocalData.no_alternate_E9_of_cross_commutator (h : LocalData d) (i j : Bool) (P : Subgroup G)
    [IsElementaryAbelian 3 P] (hPc : Nat.card P = 9)
    (hPI : P ≤ d.alternateI i j) (hd : Disjoint (d.X i) P)
    (hcross : ⁅d.Y j, d.X i⁆ ≤ (d.X i).pCoreIn 2) : False := by
  let L := d.X i
  let N := L.pCoreIn 2
  let H := normalizer (N : Set G)
  have hLH : L ≤ H := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hPH : P ≤ H := hPI.trans (h.alternate_le_core_normalizer i j hcross)
  have hNH : N ≤ H := N.le_normalizer
  have hPres : P ≤ (pResidual 2 (d.alternateI i j)).map (d.alternateI i j).subtype := by
    intro x hx
    let y : d.alternateI i j := ⟨x, hPI hx⟩
    have hy : y ^ 3 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x hx)
    exact ⟨y, mem_pResidual_of_orderOf_coprime
      (Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hy) (by decide)), rfl⟩
  have hcomm : ⁅P, L⁆ ≤ N := (commutator_mono hPres le_rfl).trans
    (h.alternate_residual_commutator_le i j hcross)
  have hN : IsPGroup 2 (N.subgroupOf H) := (L.isPGroup_pCoreIn 2).of_equiv
    (subgroupOfEquivOfLe hNH).symm
  have hcop : Nat.Coprime 3 (Nat.card (N.subgroupOf H)) := by
    obtain ⟨n, hn⟩ := hN.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  let : IsElementaryAbelian 3 (P.subgroupOf H) := IsElementaryAbelian.subgroupOf hPH
  have hc : Nat.card (P.subgroupOf H) = 3 ^ 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hPH).toEquiv).trans hPc
  have hidx : (N.subgroupOf H).relIndex (L.subgroupOf H) = 3 := by
    rw [relIndex_subgroupOf hLH]
    have heq : N.subgroupOf L = pCore 2 L :=
      comap_map_eq_self_of_injective L.subtype_injective (pCore 2 L)
    change (N.subgroupOf L).index = 3
    rw [heq]
    exact h.X_quotient_card i
  have hd' : Disjoint (L.subgroupOf H) (P.subgroupOf H) := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    exact Subtype.ext (hd.le_bot hx)
  have hcomm' : ⁅P.subgroupOf H, L.subgroupOf H⁆ ≤ N.subgroupOf H := by
    apply commutator_le.mpr
    intro p hp l hl
    exact hcomm (commutator_mem_commutator hp hl)
  have hlo := primeRank_ge_of_centralized_cyclic_section
    (N.subgroupOf H) (L.subgroupOf H) (P.subgroupOf H)
    (fun x hx => pCoreIn_le 2 L hx) hidx hcop hc hd' hcomm'
  have hhi := h.normalizer_rank i
  change primeRank 3 H ≤ 2 at hhi
  omega

/-- The genuine F* test in 15.4.23, conditional on the two still-needed
classification outputs. The E₉ and the branch implication are not record fields. -/
public theorem LocalData.generalizedFitting_ne_twoCore_of_alternate_E9
    (h : LocalData d) (i j : Bool)
    (hbranch : Theory.GroupTheory.generalizedFitting (d.I i j) = pCore 2 (d.I i j) →
      ⁅d.Y j, d.X i⁆ ≤ (d.X i).pCoreIn 2)
    (hE9 : ∃ P : Subgroup G, IsElementaryAbelian 3 P ∧ Nat.card P = 9 ∧
      P ≤ d.alternateI i j ∧ Disjoint (d.X i) P) :
    Theory.GroupTheory.generalizedFitting (d.I i j) ≠ pCore 2 (d.I i j) := by
  intro hF
  obtain ⟨P, hp, hc, hPI, hd⟩ := hE9
  let := hp
  exact h.no_alternate_E9_of_cross_commutator i j P hc hPI hd (hbranch hF)

end CFSG.Quasithin.Chapter15.Section04.Source
