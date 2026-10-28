module
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Lifting a fixed-section bound through the original moving layer

Inner action modulo a centralizer moves only the original commutator layer.
If two actors commute on the containing group and one centralizes the other's
displacement, the three-subgroup lemma places its displacement in the fixed
part of that moving layer. Lifts of the fixed quotient section then bound the
displacement together with the original kernel. No complement is chosen.

Source application: MS93 (3.3), first symplectic comparison, printed p.867.
-/

public section
open Subgroup
namespace Subgroup
variable {G V : Type*} [Group G] [Group V]

/-- Inner action modulo the original centralizer moves only the original
commutator layer, without a splitting of its containing module. -/
theorem commutator_le_moving_of_inner_mod_centralizer
    (E L Y : Subgroup G) (hn : L ≤ normalizer (E : Set G))
    (hY : Y ≤ L ⊔ centralizer (E : Set G)) : ⁅E,Y⁆ ≤ ⁅E,L⁆ := by
  have hUE : ⁅E,L⁆ ≤ E := le_normalizer_iff_commutator_le_left.mp hn
  have hCU : centralizer (E : Set G) ≤ normalizer ((⁅E,L⁆ : Subgroup G) : Set G) :=
    (centralizer_le hUE).trans (centralizer_le_normalizer _)
  have hL := normalizer_commutator_ge_right E L
  have hC : ⁅centralizer (E : Set G),E⁆ ≤ ⁅E,L⁆ :=
    (commutator_eq_bot_iff_le_centralizer.mpr le_rfl).le.trans bot_le
  rw [commutator_comm E Y]
  apply (commutator_mono hY le_rfl).trans
  exact commutator_sup_le_of_relative_normal (normalizer ((⁅E,L⁆ : Subgroup G) : Set G))
    L (centralizer (E : Set G)) E ⁅E,L⁆ le_rfl hL hCU
    (by rw [commutator_comm]) hC

/-- A three-subgroup argument places displacement in a fixed natural
section; chosen lifts of that fixed section bound it modulo the kernel. -/
theorem commutator_le_lifts_sup_kernel_of_fixed_section
    (E U A Y D : Subgroup G) (hAU : A ≤ normalizer (U : Set G))
    (f : U →* V) (σ : A → V → V)
    (hact : ∀ (a : A) (u : U),
      f ⟨(a:G)*u*(a:G)⁻¹,(mem_normalizer_iff.mp (hAU a.property) u).mp u.property⟩ =
        σ a (f u))
    (S : Set V) (hfixed : ∀ v, (∀ a, σ a v = v) → v ∈ S)
    (hlifts : ∀ v ∈ S, ∃ d : (D ⊓ U : Subgroup G), f ⟨d.val,d.property.2⟩ = v)
    (hmove : ⁅E,Y⁆ ≤ U)
    (hcomm : ⁅A,Y⁆ ≤ centralizer (E : Set G))
    (hcentral : Y ≤ centralizer ((⁅E,A⁆ : Subgroup G) : Set G)) :
    ⁅E,Y⁆ ≤ D ⊔ f.ker.map U.subtype := by
  have h1 : ⁅⁅Y,A⁆,E⁆ = ⊥ := by
    rw [commutator_comm Y A]
    exact commutator_eq_bot_iff_le_centralizer.mpr hcomm
  have h2 : ⁅⁅A,E⁆,Y⁆ = ⊥ := by
    rw [commutator_comm A E,commutator_comm ⁅E,A⁆ Y]
    exact commutator_eq_bot_iff_le_centralizer.mpr hcentral
  have hc : ⁅E,Y⁆ ≤ centralizer (A : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (commutator_commutator_eq_bot_of_rotate h1 h2)
  intro c hcE
  let u : U := ⟨c,hmove hcE⟩
  have hv : f u ∈ S := by
    apply hfixed
    intro a
    have he : (a:G)*u*(a:G)⁻¹ = u := by
      rw [hc hcE a a.property,mul_inv_cancel_right]
    have heq : (⟨(a:G)*u*(a:G)⁻¹,
      (mem_normalizer_iff.mp (hAU a.property) u).mp u.property⟩ : U) = u := Subtype.ext he
    have hh := hact a u
    rw [heq] at hh
    exact hh.symm
  obtain ⟨d,hd⟩ := hlifts (f u) hv
  let k : U := u*(⟨d.val,d.property.2⟩:U)⁻¹
  have hk : k ∈ f.ker := by
    change f k=1
    rw [map_mul,map_inv,hd,mul_inv_cancel]
  have hm := (D ⊔ f.ker.map U.subtype).mul_mem
    (mem_sup_right (mem_map_of_mem U.subtype hk)) (mem_sup_left d.property.1)
  change c*d.val⁻¹*d.val ∈ D ⊔ f.ker.map U.subtype at hm
  simpa only [inv_mul_cancel_right] using hm
end Subgroup
