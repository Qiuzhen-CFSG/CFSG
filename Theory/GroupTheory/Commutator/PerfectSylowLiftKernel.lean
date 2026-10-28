module
public import Theory.GroupTheory.Commutator.AbelianSylowLift
public import Mathlib.GroupTheory.IsPerfect

/-!
# A perfect Sylow lift has no central kernel section

An injective lift of an abelian Sylow subgroup survives quotienting by any
normal subgroup of the kernel. If the resulting kernel is central, the
central Sylow transfer theorem removes it from the derived subgroup.
Perfection therefore puts the whole original kernel in that normal subgroup.

This is the central-section elimination in the strict smaller-actor argument
of DGS, Groups and Graphs (1985), (14.9), pp.215--216.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.CentralExtension
variable {E B : Type*} [Group E] [Finite E] [Group.IsPerfect E] [Group B]
  {p : ℕ} [Fact p.Prime]

/-- In a perfect extension with an injective abelian Sylow lift, every
normal subgroup containing the kernel's displacement contains the whole kernel. -/
theorem kernel_le_of_commutator_le_of_abelian_sylow_lift
    (f : E →* B) (hk : IsPGroup p f.ker)
    (Q : Sylow p B) [IsMulCommutative Q]
    (R : Subgroup E) (hR : R.map f=(Q : Subgroup B)) (hd : R ⊓ f.ker=⊥)
    (N : Subgroup E) [N.Normal] (hN : N≤f.ker) (hc : ⁅f.ker,⊤⁆≤N) :
    f.ker≤N := by
  let q := QuotientGroup.mk' N
  let f' : E ⧸ N →* B := QuotientGroup.lift N f hN
  have he : f'.comp q=f := QuotientGroup.lift_comp_mk' N f hN
  have hker : f'.ker=f.ker.map q := QuotientGroup.ker_lift N f hN
  have hcentral : f'.ker≤center (E ⧸ N) := by
    have hc' : ⁅f'.ker,(⊤ : Subgroup (E ⧸ N))⁆=⊥ := by
      rw [hker,←map_top_of_surjective q (QuotientGroup.mk'_surjective N),←map_commutator]
      apply (Subgroup.map_eq_bot_iff _).mpr
      exact hc.trans (QuotientGroup.ker_mk' N).ge
    rw [←centralizer_univ,←coe_top]
    exact commutator_eq_bot_iff_le_centralizer.mp hc'
  have hR' : (R.map q).map f'=(Q : Subgroup B) := by
    rw [map_map,he,hR]
  have hd' : R.map q ⊓ f'.ker=⊥ := by
    apply eq_bot_iff.mpr
    rintro x ⟨⟨r,hr,rfl⟩,hfr⟩
    have hrf : r∈f.ker := by
      change f' (q r)=1 at hfr
      exact hfr
    have hr1 : r=1 := hd.le ⟨hr,hrf⟩
    simp only [hr1,map_one,mem_bot]
  have hh := kernel_inf_commutator_eq_bot_of_abelian_sylow_lift f' hcentral
    (hker ▸ hk.map q) Q (R.map q) hR' hd'
  rw [Group.IsPerfect.commutator_eq_top,inf_top_eq] at hh
  intro x hx
  have hx' : q x∈f'.ker := hker.symm ▸ mem_map_of_mem q hx
  exact (QuotientGroup.eq_one_iff x).mp (hh.le hx')

end Theory.GroupTheory.CentralExtension
