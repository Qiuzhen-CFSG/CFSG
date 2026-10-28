module
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual.NineInverter

/-!
# A moved cubic direction in the Omega residual

Full movement of the odd residual of S₃ × S₃ supplies an element that
inverts both alternating factors. One factor therefore gives a normal
order-three subgroup moved by the original actor. The statement transports
that factor through the given group isomorphism.

Source application: Aschbacher--Smith 15.2.6, printed p.1109, choosing
an invariant cubic subgroup in the elementary-nine Omega row.
-/

public section
open Subgroup
namespace SymmetricThreeProductResidual
variable {D : Type*} [Group D]

/-- A full moving two-actor moves a normal cubic direction of the residual. -/
theorem exists_normal_cubic_moved_by_full_actor
    (e : D ≃* SymmetricThreeProduct.G) (S : Sylow 2 D) (R : Subgroup D)
    (hRS : R ≤ (S : Subgroup D))
    (hm : ⁅pResidual 2 D,R⁆ = pResidual 2 D) :
    ∃ C : Subgroup D, C.Normal ∧ C ≤ pResidual 2 D ∧ Nat.card C = 3 ∧
      ¬ R ≤ centralizer (C : Set D) := by
  let F := (alternatingGroup (Fin 3)).prod (⊥ : Subgroup (Equiv.Perm (Fin 3)))
  let C := F.map e.symm.toMonoidHom
  have hF : Nat.card F = 3 := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod,
      card_bot,mul_one,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  have hC : Nat.card C = 3 := (card_map_of_injective e.symm.injective).trans hF
  have hCN : C.Normal := Normal.map inferInstance _ e.symm.surjective
  have hCR : C ≤ pResidual 2 D := by
    rw [←map_pResidual 2 e.symm,residual_eq]
    exact map_mono (prod_mono le_rfl bot_le)
  obtain ⟨r,hr,_,hinv⟩ := exists_full_residual_inverter e S R hRS hm
  refine ⟨C,hCN,hCR,hC,?_⟩
  intro hcentral
  have hbot : C = ⊥ := by
    apply C.eq_bot_iff_forall.mpr
    intro c hc
    have hi : c = c⁻¹ := by
      calc
        c = r*c*r⁻¹ := by rw [←hcentral hr c hc,mul_assoc,mul_inv_cancel,mul_one]
        _ = c⁻¹ := hinv c (hCR hc)
    have ht : c^2 = 1 := by
      calc
        c^2 = c⁻¹*c := by rw [pow_two]; exact congrArg (· * c) hi
        _ = 1 := inv_mul_cancel c
    have horder : orderOf c ∣ 1 := by
      have hd3 : orderOf c ∣ 3 := hC ▸ C.orderOf_dvd_natCard hc
      exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ht) hd3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp horder)
  rw [hbot,card_bot] at hC
  omega
end SymmetricThreeProductResidual
