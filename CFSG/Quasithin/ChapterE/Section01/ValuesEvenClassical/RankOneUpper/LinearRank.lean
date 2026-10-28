module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.Assembly
public import Theory.Comparator.Defs
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.GroupAction.ModelConjugation
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms
public import Theory.SpecificGroups.SL2.SylowConsequences

/-!
# Elementary rank in almost-simple binary PSL₂ extensions

Suppose the actual normal subgroup L is isomorphic to PSL₂(2^f), f ≥ 2,
and C_G(L) = 1. Conjugation embeds every elementary abelian two-subgroup
A of G into the full automorphism group of that matrix model. Its established
automorphism bound gives |A| ≤ 2^f, and hence Group.rank A ≤ f.
This includes the outer field automorphisms and f = 2. Neither containment
of A in L nor an innerness hypothesis is used.

The model also proves that L is nonabelian: in characteristic two the
canonical SL₂–PSL₂ quotient is an isomorphism, and the upper-unipotent
subgroup of SL₂ is not normal. For the source application take L = F*(G).
The rank argument only needs its normality and the explicit centralizer
hypothesis, so it also applies without simplicity or G = LT. The independent
simple-socle argument supplies C_G(L) = 1 in the final source assembly.

The last theorem applies the rank estimate to the literal top-component
E-generation criterion. Its E.1.2(E2) structural premise remains explicit;
this module does not claim the full E.1.14 upper bound without that premise.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.5--6 and the PSL₂ case of E.1.14(1), printed pp.210, 214. The model
automorphism calculation is the one used in GLS, Volume 2, Theorem 26.24,
Step 5 (`refs/KGroup/GLS2/ChapterG.tex`).
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- Nonabelianness follows from the actual matrix model, without a
simplicity or nonabelianness assumption on the subgroup. -/
theorem linear_socle_not_isMulCommutative (L : Subgroup G) {f : ℕ}
    (e : L ≃* PSL2Model f) : ¬ IsMulCommutative L := by
  intro h
  let d := (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 f)).trans e.symm
  let : IsMulCommutative (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    IsMulCommutative.of_comm fun a b => d.injective (by simp only [map_mul, mul_comm])
  exact Matrix.SpecialLinearGroup.upperUnipotent_not_normal (GaloisField 2 f) inferInstance

/-- Faithful conjugation controls elementary subgroups of the whole ambient
extension, including subgroups with nontrivial outer field image. -/
theorem linear_elementary_card_le (L : Subgroup G) [L.Normal] {f : ℕ}
    (hf : 2 ≤ f) (e : L ≃* PSL2Model f)
    (hC : centralizer (L : Set G) = ⊥)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 2 ^ f := by
  let ρ := Theory.GroupAction.ModelConjugation.action A L
    (le_normalizer_of_normal (H := L) (K := A)) e
  have hρ : Function.Injective ρ := by
    apply (MonoidHom.ker_eq_bot_iff ρ).mp
    rw [Theory.GroupAction.ModelConjugation.action_ker, hC]
    exact bot_subgroupOf A
  let : IsElementaryAbelian 2 A := hA
  let : IsElementaryAbelian 2 ρ.range :=
    IsElementaryAbelian.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hc : Nat.card A = Nat.card ρ.range :=
    Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv
  rw [hc]
  exact Theory.PSL2.elementary_card_le hf ρ.range

variable [Finite G]

/-- Generator rank of every elementary two-subgroup in an ambient group
acting faithfully on its specified normal PSL₂ subgroup. -/
theorem linear_elementary_rank_le_of_normal (L : Subgroup G) [L.Normal] {f : ℕ}
    (hf : 2 ≤ f) (e : L ≃* PSL2Model f)
    (hC : centralizer (L : Set G) = ⊥)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) : Group.rank A ≤ f := by
  let : IsElementaryAbelian 2 A := hA
  exact IsElementaryAbelian.rank_le_of_card_le A
    (linear_elementary_card_le L hf e hC A hA)

/-- The rank estimate at the source's literal generalized Fitting subgroup.
In particular it applies when this subgroup is simple and G = LT. -/
theorem linear_elementary_rank_le {f : ℕ} (hf : 2 ≤ f)
    (e : generalizedFitting G ≃* PSL2Model f)
    (hC : centralizer (generalizedFitting G : Set G) = ⊥)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) : Group.rank A ≤ f :=
  linear_elementary_rank_le_of_normal (generalizedFitting G) hf e hC A hA

/-- The PSL₂ rank calculation discharges the numerical premise of the
top-component E-generation criterion. The independent E2 structure must
still be supplied by the source assembly. -/
theorem linear_isEGeneratedAt_of_top_component {f : ℕ} (hf : 2 ≤ f)
    (e : generalizedFitting G ≃* PSL2Model f)
    (hC : centralizer (generalizedFitting G : Set G) = ⊥)
    (T : Sylow 2 G)
    (hcomponent : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ (T : Subgroup G) → A ≠ ⊥ → ECaseComponent (T : Subgroup G) A ⊤) :
    IsEGeneratedAt f T := by
  apply isEGeneratedAt_of_top_component_and_rank T hcomponent
  intro A hA _
  exact linear_elementary_rank_le hf e hC A hA

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper
