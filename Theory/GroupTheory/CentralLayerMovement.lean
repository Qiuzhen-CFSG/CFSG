module
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.PResidual.Quotient
public import Stellmacher.OmegaOneCenterMap

/-!
# Detecting a moving central layer from conjugate actions

If a normal subgroup W centralizes O₂(H) and O²(H), with H/O₂(H) isomorphic
to S₃, then H/C_H(W) is a two-group of order dividing six. It is cyclic,
so conjugate elements act identically on W. A pair of conjugate elements
with different actions therefore proves [W,O²(H)] is nontrivial.

Source application: Goldschmidt (6.5), radius-one central involution geometry.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {H : Type*} [Group H] [Finite H]

theorem central_layer_moved_of_conjugate_actions
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))
    (W : Subgroup H) [W.Normal]
    (hWQ : W ≤ centralizer (pCore 2 H : Set H))
    {w x g : H} (hw : w ∈ W)
    (hn : ¬ Commute w x) (hc : Commute w (g * x * g⁻¹)) :
    ⁅W, pResidual 2 H⁆ ≠ ⊥ := by
  intro htrivial
  let C := centralizer (W : Set H)
  have hQC : pCore 2 H ≤ C := le_centralizer_iff.mp hWQ
  have hRC : pResidual 2 H ≤ C := le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp htrivial)
  have htwo := (pResidual_le_iff_isPGroup_quotient 2 C).mp hRC
  have hdiv : Nat.card (H ⧸ C) ∣ 6 := by
    change C.index ∣ 6
    rw [← SymmetricThreeTwoCore.core_index e]
    exact index_dvd_of_le hQC
  have hcop : Nat.Coprime (Nat.card (H ⧸ C)) 3 := by
    obtain ⟨n, hn⟩ := htwo.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hd2 : Nat.card (H ⧸ C) ∣ 2 := hcop.dvd_mul_right.mp hdiv
  let : IsCyclic (H ⧸ C) := isCyclic_of_card_dvd_prime hd2
  let q := QuotientGroup.mk' C
  have he : q (g*x*g⁻¹) = q x := by
    simp only [map_mul, map_inv]
    rw [mul_comm (q g) (q x), mul_assoc, mul_inv_cancel, mul_one]
  have hm : (g*x*g⁻¹) / x ∈ C := QuotientGroup.eq_iff_div_mem.mp he
  have hc' : Commute w ((g*x*g⁻¹) / x) := hm w hw
  apply hn
  have hcancel : (g*x*g⁻¹)⁻¹ * ((g*x*g⁻¹) / x) = x⁻¹ := by rw [div_eq_mul_inv, inv_mul_cancel_left]
  have hh' := hc.inv_right.mul_right hc'
  rw [hcancel] at hh'
  simpa only [inv_inv] using hh'.inv_right

omit [Finite H] in
theorem omega_center_normal (Q : Subgroup H) [Q.Normal] :
    (Stellmacher.omegaOneCenterAmbient Q).Normal := by
  rw [← normalizer_eq_top_iff]
  apply top_unique
  intro g _
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (Stellmacher.omegaOneCenterAmbient Q).map (MulAut.conj g).toMonoidHom = _
  rw [← Stellmacher.omegaOneCenterAmbient_map_injective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective]
  have he : Q.map (MulAut.conj g).toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp (Q.normalizer_eq_top ▸ mem_top g)
  exact congrArg Stellmacher.omegaOneCenterAmbient he

end Theory.GroupTheory
