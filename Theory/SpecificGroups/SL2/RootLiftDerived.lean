module
public import Theory.SpecificGroups.SL2.OddBorelMarking
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Derived containment for torus-normalized rank-one root lifts

In characteristic two, every nontrivial odd subgroup of an SL2 Sylow
normalizer moves the entire Sylow by commutators. Simultaneous diagonal
coordinates reduce this to the nonzero multiplier a²-1. If a subgroup
embeds as that Sylow and is normalized by a lift of the odd subgroup,
the commutator calculation lifts inside the original root subgroup.

The actual commuting elementary DGS apartment supplies such a local
Cartan for both roots; their join is therefore perfect. This is the
nonbinary r=4 core-elimination step in DGS, Groups and Graphs (1985),
(14.9), printed p.215. No perfectness of the extension is assumed here.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups commutatorElement
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local notation "u" => transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one

/-- A nontrivial odd subgroup of a Sylow normalizer moves the whole Sylow. -/
theorem sylow_commutator_odd_normalizer (S : Sylow 2 SL(2,F))
    (C : Subgroup SL(2,F)) (hC : C ≤ normalizer (S : Set SL(2,F)))
    (ho : Odd (Nat.card C)) (hne : C ≠ ⊥) :
    ⁅(S : Subgroup SL(2,F)), C⁆ = (S : Subgroup SL(2,F)) := by
  obtain ⟨a,d,hS,hd⟩ := sylow_odd_subgroup_diagonal_coordinates S C hC ho
  let f := (MulAut.conj a).toMonoidHom
  apply Subgroup.map_injective (f := f) (MulAut.conj a).injective
  rw [map_commutator,hS,commutator_comm]
  apply le_antisymm
  · rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp (by
      have hh := (map_mono (f := f) hC).trans ((S : Subgroup SL(2,F)).le_normalizer_map f)
      simpa only [f,hS] using hh)
  · obtain ⟨c,hc,hcne⟩ := C.bot_or_exists_ne_one.resolve_left hne
    let z := d ⟨c,hc⟩
    have hz : (z:F) ≠ 1 := by
      intro he
      apply hcne
      apply (MulAut.conj a).injective
      have hh := hd ⟨c,hc⟩
      change f c=diag2 (z:F) z.ne_zero at hh
      change f c=f 1
      rw [hh,map_one]
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diag2_coe',he]
    have hsq : (z:F)^2≠1 := by
      intro he
      exact hz ((frobenius_inj F 2) (by simpa [frobenius_def] using he))
    have hzC : diag2 (z:F) z.ne_zero ∈ C.map f :=
      (hd ⟨c,hc⟩) ▸ mem_map_of_mem f hc
    intro x hx
    obtain ⟨t,rfl⟩ := (mem_upperUnipotent F x).mp hx
    rw [←commutator_diag2_transvection (z:F) z.ne_zero (t/((z:F)^2-1)) t
      (div_mul_cancel₀ t (sub_ne_zero_of_ne hsq)).symm]
    exact commutator_mem_commutator hzC ((mem_upperUnipotent F _).mpr ⟨_,rfl⟩)

/-- An injective Sylow lift normalized by a nontrivial odd quotient torus
lies in the derived subgroup of its actual ambient group. -/
theorem sylow_lift_le_commutator {E : Type*} [Group E]
    (f : E →* SL(2,F)) (R C : Subgroup E) (S : Sylow 2 SL(2,F))
    (hR : R.map f=(S : Subgroup SL(2,F))) (hk : R ⊓ f.ker=⊥)
    (hC : C ≤ normalizer (R : Set E))
    (ho : Odd (Nat.card (C.map f))) (hne : C.map f≠⊥) :
    R ≤ _root_.commutator E := by
  have hn : C.map f ≤ normalizer (S : Set SL(2,F)) := by
    change C.map f ≤ normalizer ((S : Subgroup SL(2,F)) : Set SL(2,F))
    rw [←hR]
    exact (map_mono hC).trans (R.le_normalizer_map f)
  have hm : (⁅R,C⁆).map f=R.map f := by
    rw [map_commutator,hR,sylow_commutator_odd_normalizer S (C.map f) hn ho hne]
  have hle : ⁅R,C⁆ ≤ R := le_normalizer_iff_commutator_le_left.mp hC
  intro x hx
  obtain ⟨y,hy,he⟩ := hm.symm ▸ mem_map_of_mem f hx
  have hxy : x*y⁻¹∈R ⊓ f.ker := ⟨R.mul_mem hx (R.inv_mem (hle hy)),by
    change f (x*y⁻¹)=1
    rw [map_mul,map_inv,he,mul_inv_cancel]⟩
  have hxy' : x=y := mul_inv_eq_one.mp (mem_bot.mp (hk ▸ hxy))
  rw [hxy']
  exact (commutator_mono (show R ≤ ⊤ from le_top) (show C ≤ ⊤ from le_top)) hy
end Matrix.SpecialLinearGroup
