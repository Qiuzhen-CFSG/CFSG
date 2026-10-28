module
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block.Quaternion.Geometry

/-!
# The local-core equality in G.2.4(8)

The preimage of the U-fixed space on V_L/V₁ contains V. Since V has index
two, a larger preimage would be all of V_L, contrary to the orthogonal
rank-one obstruction. Thus the preimage is V. G.2.2 places O₂(L₁)∩V_L in
this preimage. Finally the actual star images of U and O₂(L₁) agree, and
the supplied collapse identifies the star kernel inside L with V_L.
Comparing representatives proves U=O₂(L₁), without block recognition.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(8), printed pp.334–335.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Quaternion
open Setup Block
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

/-- Terminal commutator generation puts the closure inside L. -/
theorem closure_le_L (d : Hypothesis D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U) : D.U ≤ D.L :=
  (d.terminal_reduction hfull).2.trans
    ((pCoreIn_le 2 D.L₁).trans ((map_subtype_le _).trans inf_le_left))

/-- The actual closure cannot move the four-space only into its fixed point. -/
theorem first_commutator_not_le_point (d : Hypothesis D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U) : ¬ ⁅D.VL, D.U⁆ ≤ D.V₁ := by
  intro h
  have h' : ⁅D.U, D.VL⁆ ≤ D.V₁ := by rwa [commutator_comm]
  apply d.star_U_ne_bot
  apply bot_unique
  rintro _ ⟨u, hu, rfl⟩
  have he := starProjection_eq_one_of_commutator_point d
    ⟨u, closure_le_L d hfull hu⟩ (commutator_le.mp h' u hu)
  exact congrArg Subtype.val he

/-- The preimage of C_(V_L/V₁)(U) is precisely the original seed V. -/
theorem first_fixed_preimage (d : Hypothesis D g) (c : EarlierStructure D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U) :
    commutatorPreimage D.VL D.U D.V₁ = D.V := by
  let P := commutatorPreimage D.VL D.U D.V₁
  have hV : D.V ≤ D.VL := c.orthogonal_intersection.symm ▸ inf_le_left
  have hVP : D.V ≤ P := le_commutatorPreimage hV
    ((commutator_mono (le_conjugateSpanBy _ _) le_rfl).trans
      (derived_le_of_frattini_image_le d.setup.U_isPGroup d.setup.frattini_U_le_point))
  have hP : P ≤ D.VL := commutatorPreimage_le _ _ _
  have h8 : 8 ≤ Nat.card P := c.seed_card ▸ card_le_of_le hVP
  have h16 : Nat.card P ≤ 16 := c.orthogonal_card ▸ card_le_of_le hP
  have hd : Nat.card P ∣ 16 := c.orthogonal_card ▸ card_dvd_of_le hP
  have hcard : Nat.card P = 8 ∨ Nat.card P = 16 := by
    have hcases : ∀ n ∈ Finset.Icc 8 16, n ∣ 16 → n = 8 ∨ n = 16 := by decide
    exact hcases _ (Finset.mem_Icc.mpr ⟨h8,h16⟩) hd
  rcases hcard with hcard | hcard
  · exact (eq_of_le_of_card_ge hVP (by rw [hcard, c.seed_card])).symm
  · have he : P = D.VL := eq_of_le_of_card_ge hP (by rw [hcard, c.orthogonal_card])
    have hn : D.VL ≤ normalizer (D.V₁ : Set G) := by
      let := d.VL_elementary
      apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro v hv z hz
      exact congrArg Subtype.val (mul_comm' (⟨z, le_conjugateSpanBy _ _ hz⟩ : D.VL) ⟨v,hv⟩)
    have hb := commutator_commutatorPreimage_le D.VL D.U D.V₁ hn
    change ⁅P, D.U⁆ ≤ D.V₁ at hb
    rw [he] at hb
    exact (first_commutator_not_le_point d hfull hb).elim

/-- G.2.2 centrality and the fixed-space calculation control the kernel of
O₂(L₁) on the orthogonal module. -/
theorem local_core_inf_first_le_seed (d : Hypothesis D g) (c : EarlierStructure D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hcore : D.L₁.pCoreIn 2 ≤ D.QH) : D.L₁.pCoreIn 2 ⊓ D.VL ≤ D.V := by
  rw [← first_fixed_preimage d c hfull]
  exact le_commutatorPreimage inf_le_right
    ((commutator_mono (inf_le_left.trans hcore) le_rfl).trans d.local_core_commutator_closure)

/-- The original U is the complete local two-core, using its actual starred
image and the collapsed star kernel. No block recognition is assumed. -/
theorem closure_eq_local_core (d : Hypothesis D g) (c : EarlierStructure D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hcore : D.L₁.pCoreIn 2 ≤ D.QH) (hS : D.S g = D.VL) : D.U = D.L₁.pCoreIn 2 := by
  have hU := (d.terminal_reduction hfull).2
  have hL : D.L₁.pCoreIn 2 ≤ D.L :=
    (pCoreIn_le 2 D.L₁).trans ((map_subtype_le _).trans inf_le_left)
  have hstar : D.star (D.L₁.pCoreIn 2) = D.star D.U := star_local_core.trans c.star_core.symm
  apply le_antisymm hU
  intro x hx
  let q := QuotientGroup.mk' (pCore 2 D.LT)
  let x' : D.LT := ⟨x, (hL.trans le_sup_left) hx⟩
  have hxq : q x' ∈ D.star D.U := hstar ▸ mem_map_of_mem q hx
  obtain ⟨u, hu, heu⟩ := hxq
  let k : D.L := ⟨x * (u : G)⁻¹, D.L.mul_mem (hL hx) (D.L.inv_mem (closure_le_L d hfull hu))⟩
  have hkstar : starProjection D k = 1 := by
    apply Subtype.ext
    change q (x' * u⁻¹) = 1
    rw [map_mul, map_inv, heu, mul_inv_cancel]
  have hkV := mem_first_of_starProjection_eq_one c hS k hkstar
  have hkcore : (k : G) ∈ D.L₁.pCoreIn 2 :=
    (D.L₁.pCoreIn 2).mul_mem hx ((D.L₁.pCoreIn 2).inv_mem (hU hu))
  have hkU := le_conjugateSpanBy D.V D.H (local_core_inf_first_le_seed d c hfull hcore ⟨hkcore,hkV⟩)
  have hxU := D.U.mul_mem hkU hu
  change (x * (u : G)⁻¹) * (u : G) ∈ D.U at hxU
  simpa only [inv_mul_cancel_right] using hxU

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Quaternion
