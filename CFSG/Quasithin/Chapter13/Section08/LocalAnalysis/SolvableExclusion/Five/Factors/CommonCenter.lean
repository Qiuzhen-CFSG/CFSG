module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Alternatives
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.RankOne

/-!
# The common-center action on the literal image of D_H

The source kernel identity identifies Dγ with Uγ ∩ Q_H and identifies its
index with the order of Uγ*. If an element of Uγ* fixes the image of D_H,
its commutators with D_H lie in both V₁ and A₁. Disjointness of these lines
makes the commutators trivial. The F.9.16 equality C_{Uγ}(D_H)=Dγ then
proves faithfulness on that image. Normalization, the image line of order
two and the common-center displacement bound follow from the actual
commutator preimages and quotient maps.

`commonCenterOnDH_of_centralizer_equality` constructs the full geometric
record from the two source equality-case conclusions. It does not assume
faithfulness or a common-center action. Establishing the equality premise
and applying universal F.9.16(2) remain the source assembly's obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.16(2)
and its proof, printed pp.323–324; application in 13.8.13, printed p.951.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
variable {G : Type*} [Group G]
variable {H UH V₁ : Subgroup G}

theorem dgamma_eq_core_intersection (Uγ : Subgroup G)
    (hUγ : Uγ ≤ H) (hz : H ≤ normalizer (V₁ : Set G))
    (hk : Source.QH H = commutatorPreimage H UH V₁) :
    Source.Dgamma Uγ UH V₁ = Uγ ⊓ Source.QH H := by
  apply le_antisymm
  · refine le_inf (commutatorPreimage_le _ _ _) ?_
    rw [hk]
    exact le_commutatorPreimage ((commutatorPreimage_le _ _ _).trans hUγ)
      (commutator_commutatorPreimage_le Uγ UH V₁ (hUγ.trans hz))
  · apply le_commutatorPreimage inf_le_left
    apply (commutator_mono inf_le_right le_rfl).trans
    rw [hk]
    exact commutator_commutatorPreimage_le H UH V₁ hz

theorem dgamma_index_eq_star_card [Finite G] (Uγ : Subgroup G)
    (hUγ : Uγ ≤ H) (hz : H ≤ normalizer (V₁ : Set G))
    (hk : Source.QH H = commutatorPreimage H UH V₁) :
    (Source.Dgamma Uγ UH V₁).relIndex Uγ = Nat.card (Source.starImage H Uγ) := by
  rw [dgamma_eq_core_intersection Uγ hUγ hz hk, inf_relIndex_left,
    CriticalGeometry.starImage_card H Uγ hUγ]

variable [(V₁.subgroupOf UH).Normal]

/-- Faithfulness on the actual image of D_H follows from the unquotiented
centralizer equality in the F.9.16 equality case. -/
theorem StarAction.faithful_on_DH_of_centralizer_equality
    (a : StarAction H UH V₁) (Uγ A₁ : Subgroup G)
    (hUγ : Uγ ≤ H) (hz : H ≤ normalizer (V₁ : Set G))
    (hk : Source.QH H = commutatorPreimage H UH V₁)
    (hdis : Disjoint V₁ A₁)
    (hcomm : ⁅Source.DH UH Uγ A₁, Uγ⁆ ≤ A₁)
    (hc : Uγ ⊓ centralizer (Source.DH UH Uγ A₁ : Set G) =
      Source.Dgamma Uγ UH V₁) :
    ∀ b ∈ Source.starImage H Uγ,
      (∀ d ∈ tildeImage UH V₁ (Source.DH UH Uγ A₁), a.action b d = d) → b = 1 := by
  rintro b ⟨h, hh, rfl⟩ hfix
  have hcentral : (h : G) ∈ centralizer (Source.DH UH Uγ A₁ : Set G) := by
    apply mem_centralizer_iff.mpr
    intro d hd
    let u : UH := ⟨d, commutatorPreimage_le _ _ _ hd⟩
    have he := hfix (QuotientGroup.mk' (V₁.subgroupOf UH) u)
      (mem_map_of_mem _ hd)
    rw [a.conjugation] at he
    have hv := QuotientGroup.eq_iff_div_mem.mp he
    change (h : G) * d * (h : G)⁻¹ / d ∈ V₁ at hv
    have hv' : ⁅(h : G), d⁆ ∈ V₁ := by
      simpa only [commutatorElement_def, div_eq_mul_inv] using hv
    have ha : ⁅(h : G), d⁆ ∈ A₁ := by
      rw [commutator_comm] at hcomm
      exact hcomm (commutator_mem_commutator hh hd)
    have heq : ⁅(h : G), d⁆ = 1 := hdis.le_bot ⟨hv', ha⟩
    exact (commutatorElement_eq_one_iff_mul_comm.mp heq).symm
  have hD : (h : G) ∈ Source.Dgamma Uγ UH V₁ := hc ▸ ⟨hh, hcentral⟩
  rw [dgamma_eq_core_intersection Uγ hUγ hz hk] at hD
  apply (QuotientGroup.eq_one_iff h).mpr
  have hQ : (Source.QH H).subgroupOf H = pCore 2 H :=
    comap_map_eq_self_of_injective H.subtype_injective _
  rw [← hQ]
  exact hD.2

theorem tildeImage_card_of_disjoint [Finite G]
    (A : Subgroup G) (hA : A ≤ UH) (hdis : Disjoint V₁ A) :
    Nat.card (tildeImage UH V₁ A) = Nat.card A := by
  let q := QuotientGroup.mk' (V₁.subgroupOf UH)
  have hi : Function.Injective (q.subgroupMap (A.subgroupOf UH)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hz : (x : UH) ∈ V₁.subgroupOf UH :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
    apply Subtype.ext
    apply Subtype.ext
    exact hdis.le_bot ⟨hz, x.property⟩
  have hc := Nat.card_congr (MulEquiv.ofBijective
    (q.subgroupMap (A.subgroupOf UH)) ⟨hi, q.subgroupMap_surjective _⟩).toEquiv
  exact hc.symm.trans (Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv)

/-- Construct the common-center record on the literal D_H image. The only
equality-case inputs are the source centralizer equality and its index. -/
theorem commonCenterOnDH_of_centralizer_equality [Finite G]
    [IsMulCommutative UH]
    (a : StarAction H UH V₁) (Uγ A₁ : Subgroup G) [IsMulCommutative Uγ]
    (hUγ : Uγ ≤ H) (hz : H ≤ normalizer (V₁ : Set G))
    (hk : Source.QH H = commutatorPreimage H UH V₁)
    (hAU : A₁ ≤ UH) (hAγ : A₁ ≤ Uγ) (hcard : Nat.card A₁ = 2)
    (hdis : Disjoint V₁ A₁)
    (hindex : (Source.DH UH Uγ A₁).relIndex UH = (Source.Dgamma Uγ UH V₁).relIndex Uγ)
    (hactor : Nat.card (Source.starImage H Uγ) = 4)
    (hc : Uγ ⊓ centralizer (Source.DH UH Uγ A₁ : Set G) =
    Source.Dgamma Uγ UH V₁) : CommonCenterOnDH a Uγ A₁ := by
  have hindex4 : (Source.DH UH Uγ A₁).relIndex UH = 4 :=
    hindex.trans ((dgamma_index_eq_star_card Uγ hUγ hz hk).trans hactor)
  have hnA : UH ≤ normalizer (A₁ : Set G) :=
    ((UH.le_centralizer).trans (centralizer_le hAU)).trans (centralizer_le_normalizer _)
  have hγA : Uγ ≤ normalizer (A₁ : Set G) :=
    ((Uγ.le_centralizer).trans (centralizer_le hAγ)).trans (centralizer_le_normalizer _)
  have hcomm : ⁅Source.DH UH Uγ A₁, Uγ⁆ ≤ A₁ :=
    commutator_commutatorPreimage_le UH Uγ A₁ hnA
  have hnorm : Uγ ≤ normalizer (Source.DH UH Uγ A₁ : Set G) :=
    commutatorPreimage_normalized UH Uγ A₁ Uγ hnA
      (hUγ.trans a.normalizes) le_normalizer hγA
  have hAD : A₁ ≤ Source.DH UH Uγ A₁ := by
    apply le_commutatorPreimage hAU
    have he : ⁅A₁, Uγ⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (hAγ.trans Uγ.le_centralizer)
    exact he.le.trans bot_le
  refine ⟨hindex4, ?_, a.faithful_on_DH_of_centralizer_equality Uγ A₁ hUγ hz hk
    hdis hcomm hc, (tildeImage_card_of_disjoint A₁ hAU hdis).trans hcard,
    map_mono (subgroupOf_mono UH hAD), ?_⟩
  · rintro b d ⟨u, hu, rfl⟩
    obtain ⟨s, hs, he⟩ := b.property
    obtain ⟨h, hh, rfl⟩ := hs
    change (b : MulAut _) (QuotientGroup.mk' (V₁.subgroupOf UH) u) ∈ _
    rw [← he, a.conjugation]
    apply mem_map_of_mem
    exact le_normalizer_iff.mp hnorm h hh u hu
  · rw [a.commutatorSubgroup_eq_tildeImage (Source.DH UH Uγ A₁) Uγ
      (commutatorPreimage_le UH Uγ A₁) hUγ]
    exact map_mono (subgroupOf_mono UH hcomm)

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
