module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block.Inputs
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.TerminalReduction

/-!
# The last centrality step in G.2.4(8)

G.2.2 centralizes U modulo V₁ under Q_H. Consequently the source bound
S≤O₂(L₁)V_L, together with O₂(L₁)≤Q_H, centralizes S/V_L under U.
The actual upper action then has full fixed space. Clause (6) identifies
this with the image of W; disjointness from the image of Wᵍ and invariance
of S₂ force S=S₂. Once the earlier chief-factor step gives S₂=V_L,
this proves the terminal collapse.

The two earlier bounds are explicit here. Their proofs, including the
natural-module step, are required before the source implication is complete.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(8), printed pp.334–335.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup Block
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

namespace Hypothesis

/-- Since S centralizes V_L, it lies in the point stabilizer and normalizes
its characteristic residual L₁. Thus [S,L₁] is a normal two-subgroup of L₁. -/
theorem core_commutator_le_local_core (d : Hypothesis D g)
    (c : EarlierStructure D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U) :
    ⁅D.S g, D.L₁⁆ ≤ D.L₁.pCoreIn 2 := by
  have hI := d.terminal_group_eq hfull c.generated
  have hSL : D.S g ≤ D.L := (pCoreIn_le 2 (D.I g)).trans hI.le
  have hSC : D.S g ≤ centralizer (D.VL : Set G) :=
    le_centralizer_iff.mp ((d.central_first c.L_le_I).trans inf_le_right)
  have hSG : D.S g ≤ D.G₁ :=
    (hSC.trans (centralizer_le (le_conjugateSpanBy D.V₁ D.L))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hSn : D.S g ≤ normalizer (D.L₁ : Set G) :=
    (le_inf hSL hSG).trans (le_normalizer_embedded_pResidual 2 (D.L ⊓ D.G₁))
  have hlocalL : D.L₁ ≤ D.L := (map_subtype_le _).trans inf_le_left
  have hnS : D.L₁ ≤ normalizer (D.S g : Set G) :=
    (hlocalL.trans c.L_le_I).trans (I_normalizes_core D g)
  have hcS := le_normalizer_iff_commutator_le_left.mp hnS
  exact le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 (D.I g)).to_le hcS)
    (le_normalizer_iff_commutator_le_right.mp hSn)
    (normalizer_commutator_ge_right _ _)

/-- Once the natural upper action supplies full commutator generation
modulo V_L, its source containment follows in the original group. -/
theorem core_le_local_core_sup_first_of_commutator (d : Hypothesis D g)
    (c : EarlierStructure D g)
    (hfull : ⁅D.tilde D.U, D.tilde D.L₁⁆ = D.tilde D.U)
    (hcomm : D.S g = ⁅D.S g, D.L₁⁆ ⊔ D.VL) :
    D.S g ≤ D.L₁.pCoreIn 2 ⊔ D.VL := by
  rw [hcomm]
  exact sup_le_sup (d.core_commutator_le_local_core c hfull) le_rfl

/-- G.2.2's centrality in the literal tilde quotient, pulled back to G. -/
theorem local_core_commutator_closure (d : Hypothesis D g) :
    ⁅D.QH, D.U⁆ ≤ D.V₁ := by
  let q := QuotientGroup.mk' (D.V₁.subgroupOf D.G₁)
  have hQG : D.QH ≤ D.G₁ := (pCoreIn_le 2 D.H).trans d.setup.H_le
  have hUG : D.U ≤ D.G₁ := d.setup.U_le_H.trans d.setup.H_le
  have hc := d.setup.tilde_U_central.2.trans (omegaOneAmbient_le _)
  apply commutator_le.mpr
  intro x hx u hu
  let x' : D.G₁ := ⟨x, hQG hx⟩
  let u' : D.G₁ := ⟨u, hUG hu⟩
  have hxq : q x' ∈ D.tilde D.QH := mem_map_of_mem q hx
  have huq : q u' ∈ D.tilde D.U := mem_map_of_mem q hu
  obtain ⟨z, hz, he⟩ := hc huq
  change (z : D.Tilde) = q u' at he
  have hcomm : q x' * q u' = q u' * q x' := by
    have h := congrArg Subtype.val (mem_center_iff.mp hz ⟨q x', hxq⟩)
    change q x' * (z : D.Tilde) = (z : D.Tilde) * q x' at h
    rwa [he] at h
  have heq : q ⁅x', u'⁆ = 1 := by
    rw [map_commutatorElement]
    exact (show Commute (q x') (q u') from hcomm).commutator_eq
  exact (QuotientGroup.eq_one_iff ⁅x', u'⁆).mp heq

/-- This is the literal commutator bound used on printed p.335. -/
theorem core_commutator_le_first_of_bound (d : Hypothesis D g)
    (hcore : D.L₁.pCoreIn 2 ≤ D.QH)
    (hbound : D.S g ≤ D.L₁.pCoreIn 2 ⊔ D.VL) : ⁅D.S g, D.U⁆ ≤ D.VL := by
  have hlocal : D.L₁.pCoreIn 2 ≤ normalizer (D.VL : Set G) :=
    ((pCoreIn_le 2 D.L₁).trans ((map_subtype_le _).trans inf_le_left)).trans
      (L_normalizes_VL D)
  have hU : D.U ≤ normalizer (D.VL : Set G) :=
    d.setup.U_normal_in_T.1.trans d.T_normalizes_VL
  have hlocalC : ⁅D.L₁.pCoreIn 2, D.U⁆ ≤ D.VL :=
    ((commutator_mono hcore le_rfl).trans d.local_core_commutator_closure).trans
      (le_conjugateSpanBy _ _)
  have hpre : D.S g ≤ commutatorPreimage (normalizer (D.VL : Set G)) D.U D.VL :=
    hbound.trans (sup_le (le_commutatorPreimage hlocal hlocalC)
      (le_commutatorPreimage D.VL.le_normalizer
        (le_normalizer_iff_commutator_le_left.mp hU)))
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ le_rfl)

/-- Full fixed space, with the two marked complementary images from (6),
forces the actual upper quotient to vanish. -/
theorem core_eq_second_of_upper_fixed (d : Hypothesis D g)
    (c : EarlierStructure D g) {F : Type*} [Field F] {s : ℕ}
    [((S₂ D g).subgroupOf (D.S g)).Normal]
    (e : EarlierUpper D g c F s)
    (hcomm : ⁅D.S g, D.U⁆ ≤ S₂ D g) : D.S g = S₂ D g := by
  have hfix : e.natural.action.commonFixed (D.U.subgroupOf (D.I g)) = ⊤ := by
    apply top_unique
    intro x _
    rw [MonoidHom.mem_commonFixed]
    intro u hu
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((S₂ D g).subgroupOf (D.S g)) x
    rw [e.natural.action_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (u : G) * (x : G) * (u : G)⁻¹ / (x : G) ∈ S₂ D g
    have hcomm' : ⁅D.U, D.S g⁆ ≤ S₂ D g := by rwa [commutator_comm]
    simpa only [commutatorElement_def, div_eq_mul_inv] using
      commutator_le.mp hcomm' u hu x x.property
  have hWtop : upperImage D g (D.W g) = ⊤ := e.fixed.trans hfix
  have hWgbot : upperImage D g (conjugate (D.W g) g) = ⊥ := by
    have hd := e.complementary.disjoint
    rw [hWtop] at hd
    exact disjoint_top.mp hd.symm
  have hWgS : conjugate (D.W g) g ≤ D.S g := by
    rw [c.core_generated]
    exact le_sup_right
  have hWg : conjugate (D.W g) g ≤ S₂ D g := by
    have hk := (Subgroup.map_eq_bot_iff _).mp hWgbot
    rw [QuotientGroup.ker_mk'] at hk
    intro x hx
    exact hk (show (⟨x, hWgS hx⟩ : D.S g) ∈
      (conjugate (D.W g) g).subgroupOf (D.S g) from hx)
  have hn : D.I g ≤ normalizer (S₂ D g : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      ((d.second_le_core c.L_le_I).trans (pCoreIn_le 2 (D.I g)))).mp
      (d.second_normal c.L_le_I)
  have hW : D.W g ≤ S₂ D g := by
    intro w hw
    have hconj := hWg (mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hw)
    have hb := (mem_normalizer_iff.mp (hn (c.L_le_I d.g_mem)) _).mp hconj
    change g * (g⁻¹ * w * (g⁻¹)⁻¹) * g⁻¹ ∈ S₂ D g at hb
    simpa only [inv_inv, mul_assoc, mul_inv_cancel_left,
      inv_mul_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using hb
  exact le_antisymm (c.core_generated ▸ sup_le hW hWg) (d.second_le_core c.L_le_I)

/-- The source's last implication, retaining exactly the two earlier
terminal steps still to be discharged: S₂=V_L and S≤O₂(L₁)V_L. -/
theorem core_eq_first_of_terminal_bounds (d : Hypothesis D g)
    (c : EarlierStructure D g) {F : Type*} [Field F] {s : ℕ}
    [((S₂ D g).subgroupOf (D.S g)).Normal]
    (e : EarlierUpper D g c F s)
    (hcore : D.L₁.pCoreIn 2 ≤ D.QH) (hsecond : S₂ D g = D.VL)
    (hbound : D.S g ≤ D.L₁.pCoreIn 2 ⊔ D.VL) : D.S g = D.VL :=
  (d.core_eq_second_of_upper_fixed c e
    ((d.core_commutator_le_first_of_bound hcore hbound).trans le_sup_left)).trans hsecond

omit [Finite G] in
/-- After core collapse the literal W is the original seed, so clause (1)'s
index four gives order 32 without confusing it with a central-product model. -/
theorem closure_card_of_core_eq_first (c : EarlierStructure D g)
    (hS : D.S g = D.VL) : Nat.card D.U = 32 := by
  have hW : D.W g = D.V := by
    change D.U ⊓ D.S g = D.V
    rw [hS, inf_comm, c.orthogonal_intersection]
  have hc := (D.W g).subgroupOf D.U |>.index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (show D.W g ≤ D.U from inf_le_left)).toEquiv] at hc
  change (D.W g).relIndex D.U * Nat.card (D.W g) = Nat.card D.U at hc
  rw [c.closure_index, hW, c.seed_card] at hc
  exact hc.symm

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
