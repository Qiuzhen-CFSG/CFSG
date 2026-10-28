module
public import CFSG.Quasithin.ChapterG.Section03
public import Theory.SpecificGroups.BinaryLinear.LineRadical
public import Mathlib.GroupTheory.Schreier

/-!
# Full-axis recognition with trivial two-core

A full common-center group has at least four elements in dimension at least
three, so the corrected G.3.1 applies to its orbit. Its canonical block is the
whole space: a form annihilating a proper block would give a nonidentity root
fixing that block pointwise, contrary to faithfulness from the trivial two-core.
Surjectivity on the block then identifies the whole acting group with GL.

For a hyperplane axis, inverse duality turns each root into a common-center
root. Reflexivity realizes every form on the dual as evaluation at an original
vector. The full-center theorem therefore applies to the literal dual image,
and injectivity of the contragredient map returns the result to the original
actor. Neither irreducibility nor semisimplicity is assumed.

Source: Aschbacher--Smith, G.3.1, printed pp.337--338, and the full-axis
application preceding 12.2.20, printed p.802. The additional trivial-two-core
guard is explicit, as required by the corrected source-use theorem.
-/

@[expose] public noncomputable section
open Subgroup BinaryLinear BinaryTransvectionGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section03
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem root_hypotheses_of_card
    {H : Subgroup (BinaryLinear.GL V)} [Finite H] {x : V}
    (hx : x ≠ 0) (hcore : pCore 2 H = ⊥) (hc : 2 < Nat.card (rootGroup H x)) :
    Hypotheses H (MulAction.orbit H x) := by
  refine ⟨?_, ⟨x,rfl⟩, ?_⟩
  · rintro y ⟨g, rfl⟩
    exact fun he => hx (g.val.injective (he.trans (g.val.map_zero).symm))
  · intro y hy
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hy
    change 1 < Group.rank (rootQuotientImage H (g.val x))
    have hr : 2 < Nat.card (rootGroup H (g.val x)) := by
      have heq : Nat.card (rootGroup H (g.val x)) = Nat.card (rootGroup H x) := by
        rw [← rootGroup_conjugate g.property x]
        exact (Nat.card_congr ((MulAut.conj g.val).subgroupMap (rootGroup H x)).toEquiv).symm
      rwa [heq]
    let q := QuotientGroup.mk' (pCore 2 H)
    have hi : Function.Injective q := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_mk', hcore]
    have hcq : Nat.card (rootQuotientImage H (g.val x)) =
        Nat.card (rootGroup H (g.val x)) := by
      exact (Nat.card_congr (((rootGroup H (g.val x)).subgroupOf H).equivMapOfInjective q hi).toEquiv).symm.trans
        (Nat.card_congr (subgroupOfEquivOfLe (rootGroup_le H (g.val x))).toEquiv)
    let : IsElementaryAbelian 2 (rootQuotientImage H (g.val x)) :=
      rootQuotientImage_elementaryAbelian H (g.val x)
    have hbound : Nat.card (rootQuotientImage H (g.val x)) ≤
        2 ^ Group.rank (rootQuotientImage H (g.val x)) := by
      exact Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' _
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 _)))
    by_contra hn
    have hp := pow_le_pow_right' (by decide : 1 ≤ (2:ℕ)) (not_lt.mp hn)
    rw [hcq] at hbound
    omega

/-- A full root in a group with trivial two-core forces its block to be the
whole space. No irreducibility hypothesis is used. -/
theorem eq_top_of_full_center_of_twoCore_eq_bot [FiniteDimensional (ZMod 2) V]
    {H : Subgroup (BinaryLinear.GL V)} [Finite H]
    (hcore : pCore 2 H = ⊥) (hd : 3 ≤ Module.finrank (ZMod 2) V)
    (x : V) (hx : x ≠ 0) (hfull : radical (centerLine x) ≤ H) : H = ⊤ := by
  have hroot : rootGroup H x = radical (centerLine x) := inf_eq_right.mpr hfull
  have hc : 2 < Nat.card (rootGroup H x) := by
    rw [hroot, BinaryLinear.LineRadical.card x hx]
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ Module.finrank (ZMod 2) V - 1 by omega)
    omega
  have h := root_hypotheses_of_card hx hcore hc
  let Δ := MulAction.orbit H x
  let i : OrbitBlock H Δ := ⟨MulAction.orbit (generated H Δ) x, x, MulAction.mem_orbit_self x, rfl⟩
  have hxi : x ∈ i.val := MulAction.mem_orbit_self x
  let W := blockSpace H Δ i
  have hxW : x ∈ W := Submodule.subset_span hxi
  have hW : W = ⊤ := by
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    apply bot_unique
    intro f hf
    have hfx : f x = 0 := (Submodule.mem_dualAnnihilator _).mp hf x hxW
    let t := transvection x f hfx
    have ht : t ∈ rootGroup H x := by
      rw [hroot]
      exact transvection_mem (Submodule.mem_span_singleton_self x)
        (fun v hv => (Submodule.mem_dualAnnihilator _).mp ((mem_line_annihilator x f).mpr hfx) v hv)
    let a : blockGroup H Δ i := ⟨t, rootGroup_le_generated H hxi ht⟩
    have ha : spanAction H i.val a = 1 := by
      ext v
      change (v : V) + f v • x = (v : V)
      rw [(Submodule.mem_dualAnnihilator _).mp hf v v.property, zero_smul, add_zero]
    have ha1 : a = 1 := (Reduced.blockAction_injective h hcore i) (ha.trans (map_one _).symm)
    have ht1 : t = 1 := congrArg Subtype.val ha1
    by_contra hfn
    exact BinaryLinear.OuterCyclic.transvection_ne_one hx hfn hfx ht1
  have hs := (fullAction_of_hypotheses_of_twoCore_eq_bot h hcore).surjective i
  apply top_unique
  intro g _
  let e : W ≃ₗ[ZMod 2] V := (LinearEquiv.ofEq _ _ hW).trans (Submodule.topEquiv)
  let gW : BinaryLinear.GL W := e.trans (g.trans e.symm)
  obtain ⟨a,ha⟩ := hs gW
  have hag : a.val = g := by
    ext v
    have he := congrArg (fun z : BinaryLinear.GL W => (z (e.symm v) : V)) ha
    change a.val (e.symm v : V) = (e.symm (g (e (e.symm v))) : V) at he
    have heval (w : W) : e w = (w : V) := rfl
    have hev : (e.symm v : V) = v := by rw [← heval, e.apply_symm_apply]
    rw [heval, hev] at he
    simpa only [← heval, e.apply_symm_apply] using he
  exact hag ▸ generated_le H i.val a.property


/-- A full hyperplane radical becomes a full center radical under the actual
contragredient action. -/
theorem full_dual_center_of_full_axis [FiniteDimensional (ZMod 2) V]
    {H : Subgroup (BinaryLinear.GL V)} (f : DualSpace V) (hf : f ≠ 0)
    (hfull : radical f.ker ≤ H) :
    radical (centerLine f) ≤ dualGroup H := by
  intro t ht
  have htroot : t ∈ rootGroup (⊤ : Subgroup (BinaryLinear.GL (DualSpace V))) f :=
    ⟨Subgroup.mem_top _, ht⟩
  obtain ⟨_, F, hFf, rfl⟩ := (mem_rootGroup_iff hf).mp htroot
  let w := (Module.evalEquiv (ZMod 2) V).symm F
  have hw : f w = 0 := (Module.apply_evalEquiv_symm_apply _ _ f F).trans hFf
  have he : contragredient (transvection w f hw) = transvection f F hFf := by
    ext l v
    change l (v + f v • w) = l v + F l • f v
    rw [map_add, map_smul, Module.apply_evalEquiv_symm_apply]
    exact congrArg (fun z : ZMod 2 => l v + z) (mul_comm (f v) (F l))
  refine ⟨transvection w f hw, hfull ?_, he⟩
  exact transvection_mem hw le_rfl

/-- A full axis group in dimension at least three, with trivial intrinsic
two-core, forces the original faithful actor to be the whole linear group. -/
theorem eq_top_of_full_axis_of_twoCore_eq_bot [FiniteDimensional (ZMod 2) V]
    {H : Subgroup (BinaryLinear.GL V)} [Finite H]
    (hcore : pCore 2 H = ⊥) (hd : 3 ≤ Module.finrank (ZMod 2) V)
    (f : DualSpace V) (hf : f ≠ 0) (hfull : radical f.ker ≤ H) : H = ⊤ := by
  have hdual : dualGroup H = ⊤ := eq_top_of_full_center_of_twoCore_eq_bot
    (dualGroup_twoCore_eq_bot hcore) (by simpa only [DualSpace, Subspace.dual_finrank_eq] using hd)
    f hf (full_dual_center_of_full_axis f hf hfull)
  apply top_unique
  intro t _
  obtain ⟨s,hs,he⟩ := hdual.ge (Subgroup.mem_top (contragredient t))
  exact contragredient_injective he ▸ hs

end CFSG.Quasithin.ChapterG.Section03
