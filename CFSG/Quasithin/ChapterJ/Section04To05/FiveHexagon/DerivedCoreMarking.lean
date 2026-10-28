module

public import CFSG.Quasithin.ChapterJ.Section04To05.SecondParabolic.Structure
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore

/-!
# Recovering the original natural eight-group from the second core

The derived subgroup of A lies in the original S₂, because R₂/S₂ is
abelian. It is normalized by S since A is normalized by G₂. If its order
exceeds eight, the genuine J.2.3 commutator theorem forces it to contain V.
The original V centralizes S, so an eight-element upper bound on its center
identifies that center exactly with the original V. The concrete root model
supplies these two intrinsic order bounds in the subsequent consumer.
Source: J.2.3(6), J.4.4(1--2), and J.4.7, printed pp.433,441,444.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
open Subgroup
open scoped commutatorElement
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} (p:Plane d)
  (B5:Sylow 5 d.toTypeRuSetup.H)

/-- The literal derived subgroup of the original A. -/
@[expose]
def sourceDerived : Subgroup G := ⁅p.A B5,p.A B5⁆

theorem sourceDerived_le_S₂ : sourceDerived p B5≤p.S₂ := by
  apply commutator_le.mpr
  intro a ha b hb
  let aa:p.parabolic:=⟨a,p.A_le_parabolic B5 ha⟩
  let bb:p.parabolic:=⟨b,p.A_le_parabolic B5 hb⟩
  apply (p.secondMap_eq_one ⁅aa,bb⁆).mp
  rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
  let := p.secondBar_R₂_elementary
  have hma : p.secondMap aa∈p.secondBar p.R₂ := ⟨aa,p.A_le_R₂ B5 ha,rfl⟩
  have hmb : p.secondMap bb∈p.secondBar p.R₂ := ⟨bb,p.A_le_R₂ B5 hb,rfl⟩
  exact congrArg Subtype.val (mul_comm' (⟨p.secondMap aa,hma⟩:p.secondBar p.R₂)
    ⟨p.secondMap bb,hmb⟩)

theorem sourceDerived_normalized : p.parabolic≤normalizer (sourceDerived p B5:Set G) := by
  intro g hg
  have hA := mem_normalizer_iff_map_conj_eq.mp (p.A_normalized B5 hg)
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [sourceDerived,Subgroup.map_commutator,hA]

/-- Every large enough derived source core contains the original natural V,
by the already proved full commutator conclusion of J.2.3. -/
theorem V_le_sourceDerived (hcard:8<Nat.card (sourceDerived p B5)) :
    d.V≤sourceDerived p B5 := by
  have hnot : ¬sourceDerived p B5≤d.V := by
    intro hh
    have hc:=card_le_of_le hh
    rw [d.ru1.card_V] at hc
    omega
  obtain ⟨z,hz,hzV⟩ := SetLike.not_le_iff_exists.mp hnot
  have hDS := (sourceDerived_le_S₂ p B5).trans p.S₂_le_S
  have hfull := SpecialCore.CommutatorGeometry.full_commutator d
    (d.parabolic_core_eq_R₁.symm.trans d.Q_sup_S_eq_parabolic_core.symm)
    d.parabolic_core_eq_R₁ ⟨z,hDS hz⟩ hzV
  rw [← hfull]
  exact (commutator_mono (zpowers_le.mpr hz) le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp
      (p.S_le_parabolic.trans (sourceDerived_normalized p B5)))

/-- Intrinsic center bounds recover V with its original ambient embedding. -/
theorem center_sourceDerived_eq_V
    (hcard:8<Nat.card (sourceDerived p B5))
    (hcenter:Nat.card (center (sourceDerived p B5))≤8) :
    (center (sourceDerived p B5)).map (sourceDerived p B5).subtype=d.V := by
  have hVD:=V_le_sourceDerived p B5 hcard
  have hDS:sourceDerived p B5≤d.toTypeRuSetup.S := (sourceDerived_le_S₂ p B5).trans p.S₂_le_S
  have hVC:d.V≤(center (sourceDerived p B5)).map (sourceDerived p B5).subtype := by
    intro v hv
    refine ⟨⟨v,hVD hv⟩,mem_center_iff.mpr ?_,rfl⟩
    intro a
    exact Subtype.ext (d.ru1.central_V hv a (hDS a.property))
  apply (eq_of_le_of_card_ge hVC ?_).symm
  rw [card_map_of_injective (sourceDerived p B5).subtype_injective,d.ru1.card_V]
  exact hcenter

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
