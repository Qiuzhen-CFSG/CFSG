module

public import Theory.SpecificGroups.SL2.RootLiftDerived
public import Theory.SpecificGroups.SL2.OppositeTwoSubgroups

/-!
# Full movement of a faithful original root lift

A root-sized two-subgroup disjoint from the full kernel maps to a Sylow
of the actual linear quotient. Its nontrivial odd normalizer moves the
whole Sylow, and faithfulness on the original root lifts the equality.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {E F : Type*} [Group E] [Field F] [Finite F] [CharP F 2]

/-- The original faithful root is its entire commutator with the actual
odd quotient-normalizer lift. -/
theorem faithful_root_commutator_eq (q : E →* SL(2,F)) (R C : Subgroup E)
    (hR : IsPGroup 2 R) (hc : Nat.card R=Nat.card F) (hk : Disjoint R q.ker)
    (hn : C≤normalizer (R:Set E))
    (ho : Odd (Nat.card (C.map q))) (hne : C.map q≠⊥) : ⁅R,C⁆=R := by
  obtain ⟨S,hS⟩ := two_subgroup_image_is_sylow q R hR hc hk.eq_bot
  have hn' : C.map q≤normalizer (S:Set SL(2,F)) := by
    change C.map q≤normalizer ((S:Subgroup SL(2,F)):Set SL(2,F))
    rw [hS]
    exact (map_mono hn).trans (R.le_normalizer_map q)
  have hm : (⁅R,C⁆).map q=R.map q := by
    rw [map_commutator,←hS,sylow_commutator_odd_normalizer S (C.map q) hn' ho hne]
  have hle : ⁅R,C⁆≤R := le_normalizer_iff_commutator_le_left.mp hn
  apply le_antisymm hle
  intro x hx
  obtain ⟨y,hy,he⟩ := hm.symm ▸ mem_map_of_mem q hx
  have hxy : x*y⁻¹∈R⊓q.ker := ⟨R.mul_mem hx (R.inv_mem (hle hy)),by
    change q (x*y⁻¹)=1
    rw [map_mul,map_inv,he,mul_inv_cancel]⟩
  have hxy' : x=y := mul_inv_eq_one.mp (hk.le_bot hxy)
  rwa [hxy']

end Matrix.SpecialLinearGroup
