module

public import Theory.SpecificGroups.Tits.EscapingSylowOvergroups
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FirstQuotient
public import Theory.GroupTheory.CoreCentralNormalizerAction.QuinticInnerSubgroup
import all Theory.GroupTheory.CoreCentralNormalizerAction.QuinticInnerSubgroup

/-!
# The actual quintic Sylow product in the Tits group

A normalized subgroup with two-core quotient five, together with the supplied
full Sylow two-subgroup, is the actual first parabolic under a Sylow marking.
The second parabolic has no factor five; the index-five first parabolic has
no intermediate subgroup with a factor five. Its canonical quotient is Sz(2),
and its full two-core has order 512.

The internal import reuses the original quintic-product cardinality lemma;
it does not change the frozen source-facing interface. This result retains
all subgroups and does not assert generic elementary-subgroup fusion escape.
Source: Parrott (1972), pp.672,683; Aschbacher--Smith 6.1.4, pp.665--666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Tits
open ExceptionalParabolics

/-- The original normalized quintic product is the marked first parabolic,
with its actual full two-core and canonical Suzuki quotient. -/
theorem quintic_sylow_product_structure
    {G : Type*} [Group G] (e : G ≃* ParrottGroup)
    (P : Sylow 2 G) (Y : Subgroup G)
    (hPY : (P : Subgroup G) ≤ normalizer (Y : Set G))
    (hfive : Nat.card (Y ⧸ pCore 2 Y) = 5) :
    let H := Y ⊔ (P : Subgroup G)
    (∃ f : G ≃* Atlas1600Group,
      (P : Subgroup G).map f.toMonoidHom = S ∧ H.map f.toMonoidHom = first) ∧
    Nat.card (pCore 2 H) = 512 ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) := by
  let : Finite G := Finite.of_equiv ParrottGroup e.symm.toEquiv
  let H := Y ⊔ (P : Subgroup G)
  obtain ⟨a,ha⟩ := Theory.GroupTheory.quintic_normalized_join_card Y
    (P : Subgroup G) P.isPGroup' hPY hfive
  have hH : H ≠ ⊤ := by
    intro hh
    have hc : Nat.card H = 17971200 := by
      rw [hh,card_top]
      exact (Nat.card_congr e.toEquiv).trans parrottGroup_card
    have hd : 3 ∣ 2^a * 5 := by rw [←ha,hc]; norm_num
    rcases Nat.prime_three.dvd_mul.mp hd with hd | hd
    · exact (by decide : ¬3∣2) (Nat.prime_three.dvd_of_dvd_pow hd)
    · norm_num at hd
  obtain ⟨f,hf⟩ := RelativeSylowMarking.exists_sylow_marking
    (e.trans parrottFiniteImageEquiv) P
  let D := H.map f.toMonoidHom
  have hSD : S ≤ D := by
    rw [S,←hf]
    exact map_mono (show (P : Subgroup G) ≤ H from le_sup_right)
  have hD : D ≠ ⊤ := by
    intro hd
    apply hH
    apply map_injective (f := f.toMonoidHom) f.injective
    exact hd.trans (map_top_of_surjective f.toMonoidHom f.surjective).symm
  have h5D : 5 ∣ Nat.card D := by
    rw [card_map_of_injective f.injective,ha]
    exact dvd_mul_left 5 _
  have hDF : D ≤ first := by
    rcases ConverseLocalCoverage.le_first_or_second D hD hSD with hh | hh
    · exact hh
    · have hd := h5D.trans (card_dvd_of_le hh)
      rw [second_card] at hd
      norm_num at hd
  have hcardD : Nat.card D = 10240 := by
    apply Nat.dvd_antisymm
    · exact first_card ▸ card_dvd_of_le hDF
    · have hd : 2048 ∣ Nat.card D := sylow_card ▸ card_dvd_of_le hSD
      exact (by decide : Nat.Coprime 2048 5).mul_dvd_of_dvd_of_dvd hd h5D
  have heq : D = first := eq_of_le_of_card_ge hDF (by rw [hcardD,first_card])
  let eh : H ≃* first := (H.equivMapOfInjective f.toMonoidHom f.injective).trans
    (MulEquiv.subgroupCongr heq)
  have hcore : (pCore 2 H).map eh.toMonoidHom = pCore 2 first := pCore_map_iso 2 eh
  refine ⟨⟨f,hf,heq⟩,?_,⟨?_⟩⟩
  · rw [←card_map_of_injective (f := eh.toMonoidHom) eh.injective,hcore]
    exact FirstQuotient.core_card
  · exact (QuotientGroup.congr _ _ eh hcore).trans FirstQuotient.coreQuotientEquiv

end Tits
