module
public import Theory.GroupTheory.Commutator.CentralSylowTransfer

/-!
# Central kernels with an abelian Sylow lift

If a central p-kernel admits an injective lift of an abelian Sylow subgroup,
then the full Sylow preimage is abelian. Central Sylow transfer consequently
removes the kernel from the derived subgroup of the extension. The extension
itself need not be perfect and its kernel need not be trivial.

Source application: DGS, Groups and Graphs (1985), (14.9), p.215, the
central-kernel step for the opposite-root actor in the r=4 case.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.CentralExtension
variable {E B : Type*} [Group E] [Finite E] [Group B]
  {p : ℕ} [Fact p.Prime]

/-- An injective abelian Sylow lift eliminates a central p-kernel from the
derived subgroup, without assuming perfection of the extension. -/
theorem kernel_inf_commutator_eq_bot_of_abelian_sylow_lift
    (f : E →* B) (hc : f.ker ≤ center E) (hk : IsPGroup p f.ker)
    (Q : Sylow p B) [IsMulCommutative Q]
    (R : Subgroup E) (hR : R.map f=(Q : Subgroup B)) (hd : R ⊓ f.ker=⊥) :
    f.ker ⊓ _root_.commutator E=⊥ := by
  have hRR : ⁅R,R⁆=⊥ := by
    have hm : (⁅R,R⁆).map f=⊥ := by
      rw [map_commutator,hR,commutator_self_eq_bot_iff.mpr inferInstance]
    apply bot_unique
    exact (le_inf (le_normalizer_iff_commutator_le_left.mp R.le_normalizer)
      ((Subgroup.map_eq_bot_iff _).mp hm)).trans hd.le
  let P := Q.comapOfKerIsPGroup f hk (hR ▸ map_le_range f R)
  have hP : (P : Subgroup E)=R ⊔ f.ker := by
    change (Q : Subgroup B).comap f=R ⊔ f.ker
    rw [←hR,comap_map_eq]
  have hPP : ⁅(P : Subgroup E),(P : Subgroup E)⁆=⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [hP]
    apply sup_le
    · apply le_centralizer_iff.mpr
      apply sup_le (commutator_eq_bot_iff_le_centralizer.mp hRR)
      exact hc.trans (center_le_centralizer _)
    · exact hc.trans (center_le_centralizer _)
  apply (f.ker ⊓ _root_.commutator E).eq_bot_iff_forall.mpr
  intro x hx
  exact mem_bot.mp (hPP ▸ center_inf_commutator_inf_sylow_le_commutator P
    ⟨⟨hc hx.1,hx.2⟩,hk.le_sylow_of_normal P hx.1⟩)
end Theory.GroupTheory.CentralExtension
