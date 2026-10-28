module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentRigidity.LocalProduct
public import Theory.GroupTheory.PResidual.SylowIndexThree
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentRigidity.RemainingBranch
/-!
# Goldschmidt rigidity when either vertex fails characteristic two

If the opposite vertex fails characteristic two, its Sylow three-subgroup
centralizes the opposite two-core. In the literal source subgroup Y=Q2L1,
the intrinsic two-core of O²(Y) is normal and lies in Q2, since Q2 is Sylow.
It is therefore invariant under that Sylow three-subgroup, and F.6.12 kills
it. The original left residual consequently has order three.

Combined with the direct exceptional-left result, this proves the cubic
and small elementary-Sylow conclusions for either exceptional vertex.
The only remaining source branch has both vertices of characteristic two
and actual left residual A4. Source: Aschbacher--Smith F.6.12--13 and F.6.17,
printed pp.307,309.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}
theorem left_residual_cubic_of_right_not_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (X : Subgroup G) [X.Normal]
    (h₁ : (pResidual 2 G₁).map G₁.subtype ≤ X)
    (h₂ : ¬ (pResidual 2 G₂).map G₂.subtype ≤ X)
    (hbad : generalizedFitting G₂ ≠ pCore 2 G₂) :
    Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3 := by
  classical
  let Q := (pCore 2 G₂).map G₂.subtype
  let L := (pResidual 2 G₁).map G₁.subtype
  let Y := Q ⊔ L
  obtain ⟨hres, S, hS, hi⟩ := normal_subgroup_local_product_setup h X h₁ h₂
  change (pResidual 2 Y).map Y.subtype = L at hres
  change (S : Subgroup Y).map Y.subtype = Q at hS
  let R := pResidual 2 Y
  let A' := (pCore 2 R).map R.subtype
  let A := A'.map Y.subtype
  have hAQ : A ≤ Q := (map_mono (f := Y.subtype)
    ((pCore_isPGroup.map R.subtype).le_sylow_of_normal S)).trans_eq hS
  have hAN : (A.subgroupOf Y).Normal := by
    change (A'.map Y.subtype).subgroupOf Y |>.Normal
    rw [subgroupOf, comap_map_eq_self_of_injective Y.subtype_injective]
    infer_instance
  let D : Sylow 3 G₂ := Classical.choice inferInstance
  have hDR : (D : Subgroup G₂) ≤ pResidual 2 G₂ := by
    intro x hx
    have hp := D.isPGroup'.orderOf_coprime (by decide : Nat.Coprime 3 2) (⟨x, hx⟩ : D)
    rw [← orderOf_coe (⟨x, hx⟩ : D)] at hp
    exact mem_pResidual_of_orderOf_coprime hp.symm
  have hDN : (D : Subgroup G₂).map G₂.subtype ≤ normalizer (A : Set G) :=
    ((map_mono hDR).trans (le_centralizer_iff.mp
      (h.symm.local_core_centralizes_residual hbad))).trans
        ((centralizer_le hAQ).trans (Subgroup.centralizer_le_normalizer _))
  have hAbot := h.right_invariant_subgroup_eq_bot hcore D A hAQ hDN hAN
  have hcoreR : pCore 2 R = ⊥ := by
    apply map_injective R.subtype_injective
    apply map_injective Y.subtype_injective
    simpa only [Subgroup.map_bot] using hAbot
  have hcard := residual_core_quotient_card_of_sylow_index_three S hi
  change Nat.card (R ⧸ pCore 2 R) = 3 at hcard
  rw [hcoreR, Nat.card_congr QuotientGroup.quotientBot.toEquiv] at hcard
  change Nat.card L = 3
  rw [← hres, Nat.card_congr (equivMapOfInjective R Y.subtype Y.subtype_injective).symm.toEquiv]
  exact hcard
end CFSG.Quasithin.ChapterF.SourceAssembly

namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

theorem left_not_characteristic_two_of_residual_cubic
    (h : IsGoldschmidtTriple G₁ G₂)
    (hc : Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3) :
    generalizedFitting G₁ ≠ pCore 2 G₁ := by
  have hcard : Nat.card (pResidual 2 G₁) = 3 :=
    (Nat.card_congr (equivMapOfInjective (pResidual 2 G₁)
      G₁.subtype G₁.subtype_injective).toEquiv).trans hc
  intro hg
  have ho := (SymmetricThreeTwoCore.characteristic_two_iff h.quotient_left.some).mp hg
  have hle : pResidual 2 G₁ ≤ pPrimeCore 2 G₁ :=
    le_sSup ⟨inferInstance, by rw [hcard]; decide⟩
  have he : pResidual 2 G₁ = ⊥ := le_bot_iff.mp (hle.trans_eq ho)
  have hh := card_eq_one.mpr he
  omega

theorem left_residual_cubic_of_either_not_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (X : Subgroup G) [X.Normal]
    (h₁ : (pResidual 2 G₁).map G₁.subtype ≤ X)
    (h₂ : ¬ (pResidual 2 G₂).map G₂.subtype ≤ X)
    (hbad : generalizedFitting G₁ ≠ pCore 2 G₁ ∨ generalizedFitting G₂ ≠ pCore 2 G₂) :
    Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3 := by
  rcases hbad with hbad | hbad
  · exact (Nat.card_congr (equivMapOfInjective (pResidual 2 G₁)
      G₁.subtype G₁.subtype_injective).symm.toEquiv).trans (h.local_residual_order_three hbad)
  · exact left_residual_cubic_of_right_not_characteristic_two h hcore X h₁ h₂ hbad

theorem SingleResidualComponent.small_sylow_of_either_exceptional
    (d : SingleResidualComponent G₁ G₂)
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hbad : generalizedFitting G₁ ≠ pCore 2 G₁ ∨ generalizedFitting G₂ ≠ pCore 2 G₂) :
    Nonempty (((pResidual 2 G₁).map G₁.subtype) ≃* Multiplicative (ZMod 3)) ∧
      IsElementaryAbelian 2 ((pCore 2 G₂).map G₂.subtype) ∧
      primeRank 2 ((pCore 2 G₂).map G₂.subtype) ≤ 3 ∧
      IsSimpleGroup (d.component ⧸ center d.component) ∧
      ∃ S : Sylow 2 (d.component ⧸ center d.component),
        IsElementaryAbelian 2 S ∧ Nat.card S ≤ 8 := by
  let : d.component.Normal := d.normal
  have hc := left_residual_cubic_of_either_not_characteristic_two h hcore d.component
    d.left_contains d.right_escapes hbad
  exact d.small_sylow_of_exceptional_left h hcore (left_not_characteristic_two_of_residual_cubic h hc)
end CFSG.Quasithin.ChapterF.SourceAssembly

namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- The actual normal-X source leaves only the both-characteristic-two
A4 case for the amalgam geometry step of F.6.13. -/
theorem normal_subgroup_left_residual_cubic_or_both_characteristic_two
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (X : Subgroup G) [X.Normal]
    (h₁ : (pResidual 2 G₁).map G₁.subtype ≤ X)
    (h₂ : ¬ (pResidual 2 G₂).map G₂.subtype ≤ X) :
    Nat.card ((pResidual 2 G₁).map G₁.subtype) = 3 ∨
      (generalizedFitting G₁ = pCore 2 G₁ ∧ generalizedFitting G₂ = pCore 2 G₂ ∧
        Nonempty (((pResidual 2 G₁).map G₁.subtype) ≃* alternatingGroup (Fin 4))) := by
  classical
  by_cases hl : generalizedFitting G₁ = pCore 2 G₁
  · by_cases hr : generalizedFitting G₂ = pCore 2 G₂
    · rcases normal_subgroup_left_residual_cubic_or_alternating_four h hcore X h₁ h₂ with hc | ha
      · obtain ⟨e⟩ := hc
        exact Or.inl ((Nat.card_congr e.toEquiv).trans (by simp))
      · exact Or.inr ⟨hl, hr, ha⟩
    · exact Or.inl (left_residual_cubic_of_right_not_characteristic_two h hcore X h₁ h₂ hr)
  · exact Or.inl (left_residual_cubic_of_either_not_characteristic_two h hcore X h₁ h₂ (Or.inl hl))

end CFSG.Quasithin.ChapterF.SourceAssembly
