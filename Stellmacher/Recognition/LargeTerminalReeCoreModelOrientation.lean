module

public import Stellmacher.Recognition.LargeTerminalFiveFixedConjugateGeometry
public import Theory.SpecificGroups.ReeTwo.CoreRootConjugacy

/-!
# The root orientation obstruction in actual terminal core coordinates

The second local group acts on its actual two-core. An explicit identification
with the verified Ree core transports this action to core automorphisms; it
does not identify that action with the specified model complement. The two
core classes of the fixed root are distinguished by the polynomial
`b9 + b5*b8 + b6*b7`. We transport the exact class criterion to the actual
local group and reduce the required exclusion of inversion to preservation
of its zero value.

The preservation premise remains explicit. As a separate geometric input,
the actual first core has an automorphism moving the distinguished central
involution: otherwise that line is normal in the generated pair, contradicting
its trivial two-core. This excludes any first-core model fixing that involution.
The connection from inversion to such a model remains to be established; an arbitrary core automorphism need not preserve it. No
conclusion about the sign of the actual action is assumed in its definition.

Sources: Thompson VI, pp.629–630, for the terminal configuration; Shinoda
(1975), (2.3), pp.81–82, for the verified core multiplication.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup
universe u

/-- Conjugation by the actual second local group, in the supplied coordinates. -/
@[expose] public def LargeTerminalContext.reeCoreAction
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (eQ : twoCoreIn ctx.second ≃* ReeTwo.Core) :
    ctx.second →* MulAut ReeTwo.Core :=
  (MulAut.congr eQ).toMonoidHom.comp
    ((twoCoreIn ctx.second).normalizerMonoidHom.comp
      (inclusion ((normal_subgroupOf_iff_le_normalizer (twoCoreIn_le ctx.second)).mp
        (twoCoreIn_normal ctx.second))))

/-- The coordinate action is literally ambient conjugation on the core. -/
public theorem LargeTerminalContext.reeCoreAction_apply
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (eQ : twoCoreIn ctx.second ≃* ReeTwo.Core)
    (b : ctx.second) (q : twoCoreIn ctx.second) :
    (eQ.symm (ctx.reeCoreAction eQ b (eQ q)) : G) =
      (b : G) * (q : G) * (b : G)⁻¹ := by
  change (eQ.symm (eQ ((twoCoreIn ctx.second).normalizerMonoidHom
    _ (eQ.symm (eQ q)))) : G) = _
  rw [eQ.symm_apply_apply, eQ.symm_apply_apply]
  rfl

/-- The exact two-class coordinate test, transported through the actual core
identification. This needs no choice of complement or squaring witness. -/
public theorem LargeTerminalContext.ree_core_isConj_iff_coordinates
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (eQ : twoCoreIn ctx.second ≃* ReeTwo.Core)
    (t q : twoCoreIn ctx.second) (ht : eQ t = ReeTwo.Core.root 2) :
    IsConj t q ↔
      (eQ q).b0 = 0 ∧ (eQ q).b1 = 0 ∧ (eQ q).b2 = 1 ∧
        (eQ q).b3 = 0 ∧ (eQ q).b4 = 0 ∧ ReeTwo.Core.rootOrientation (eQ q) = 0 := by
  rw [← ReeTwo.Core.isConj_root_two_iff, ← ht]
  constructor
  · exact eQ.toMonoidHom.map_isConj
  · intro h
    simpa only [MulEquiv.coe_toMonoidHom, eQ.symm_apply_apply] using
      eQ.symm.toMonoidHom.map_isConj h

/-- A zero orientation for the actual local action excludes inversion.
Establishing the premise from the terminal geometry is the remaining step. -/
public theorem LargeTerminalContext.ree_no_local_inversion_of_orientation
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (eQ : twoCoreIn ctx.second ≃* ReeTwo.Core)
    (t : twoCoreIn ctx.second) (ht : eQ t = ReeTwo.Core.root 2)
    (horientation : ∀ b : ctx.second,
      ReeTwo.Core.rootOrientation (ctx.reeCoreAction eQ b (ReeTwo.Core.root 2)) = 0) :
    ∀ b ∈ ctx.second, b * (t : G) * b⁻¹ ≠ (t : G)⁻¹ := by
  intro b hb hinv
  let bP : ctx.second := ⟨b, hb⟩
  have he : eQ.symm (ctx.reeCoreAction eQ bP (eQ t)) = t⁻¹ := by
    apply Subtype.ext
    exact (ctx.reeCoreAction_apply eQ bP t).trans hinv
  have hm := congrArg eQ he
  simp only [eQ.apply_symm_apply, map_inv, ht] at hm
  have ho := horientation bP
  rw [hm, ReeTwo.Core.rootOrientation_root_two_inv] at ho
  exact (by decide : (1 : ZMod 2) ≠ 0) ho

/-- In the actual local group the orientation equation is equivalent to
excluding inversion, since any conjugator in the core can be removed inside
that same local group. This is a reduction, not a geometric sign assertion. -/
public theorem LargeTerminalContext.ree_orientation_iff_no_local_inversion
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (eQ : twoCoreIn ctx.second ≃* ReeTwo.Core)
    (t : twoCoreIn ctx.second) (ht : eQ t = ReeTwo.Core.root 2) :
    (∀ b : ctx.second,
      ReeTwo.Core.rootOrientation (ctx.reeCoreAction eQ b (ReeTwo.Core.root 2)) = 0) ↔
      ∀ b ∈ ctx.second, b * (t : G) * b⁻¹ ≠ (t : G)⁻¹ := by
  refine ⟨ctx.ree_no_local_inversion_of_orientation eQ t ht, ?_⟩
  intro hno b
  let a := ctx.reeCoreAction eQ b
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1)
      (ReeTwo.Core.rootOrientation (a (ReeTwo.Core.root 2))) with ho | ho
  · exact ho
  · obtain ⟨h0, h1, h2, h3, h4⟩ := ReeTwo.Core.aut_root_two_head a
    have hc := (ReeTwo.Core.isConj_root_two_inv_iff _).mpr
      ⟨h0, h1, h2, h3, h4, ho⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp hc
    let q := eQ.symm g
    have he : (q : G) * (t : G)⁻¹ * (q : G)⁻¹ =
        (b : G) * (t : G) * (b : G)⁻¹ := by
      have hh := congrArg (fun x => (eQ.symm x : G)) hg
      rw [← ht] at hh
      simp only [map_mul, map_inv, eQ.symm_apply_apply, coe_mul, coe_inv] at hh
      exact hh.trans (ctx.reeCoreAction_apply eQ b t)
    have hmem : (q : G)⁻¹ * (b : G) ∈ ctx.second :=
      ctx.second.mul_mem (ctx.second.inv_mem (twoCoreIn_le ctx.second q.property)) b.property
    apply False.elim
    apply hno _ hmem
    calc
      ((q : G)⁻¹ * (b : G)) * (t : G) * ((q : G)⁻¹ * (b : G))⁻¹ =
          (q : G)⁻¹ * ((b : G) * (t : G) * (b : G)⁻¹) * (q : G) := by group
      _ = (t : G)⁻¹ := by rw [← he]; group

/-- The distinguished central involution belongs to the actual first core. -/
public theorem LargeTerminalContext.central_involution_mem_first_core {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (z : G)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    z ∈ twoCoreIn ctx.first := by
  have hzW : z ∈ omegaOneCenter (S : Subgroup G) := hgen ▸ mem_zpowers z
  have hzS : z ∈ (S : Subgroup G) := (map_subtype_le _) hzW
  have hSP : (S : Subgroup G) ≤ ctx.first :=
    ctx.terminal.hypothesisTwo.fiveOne.P1_mem.1.2.1.1
  have hchar := (lemma_five_three S (S : Subgroup G) ctx.first ctx.second
    ctx.terminal.hypothesisTwo).2.1
  have hzP : (⟨z, hSP hzS⟩ : ctx.first) ∈ pCore 2 ctx.first := by
    apply hchar
    apply mem_centralizer_iff.mpr
    intro q hq
    apply Subtype.ext
    have hqS : (q : G) ∈ (S : Subgroup G) :=
      (pCore_isPGroup (p := 2) (G := ctx.first)).le_sylow_of_normal (S.subtype hSP) hq
    exact mem_centralizer_iff.mp
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _) hzW) q hqS
  exact mem_map_of_mem ctx.first.subtype hzP


/-- The original pair forces a first-core automorphism to move the central
involution. A core model in which this involution is characteristic therefore
cannot be the actual neighboring core. -/
public theorem LargeTerminalContext.first_core_aut_moves_central_involution {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (z : twoCoreIn ctx.first)
    (hz : orderOf (z : G) = 2)
    (hgen : zpowers (z : G) = omegaOneCenter (S : Subgroup G)) :
    ∃ a : MulAut (twoCoreIn ctx.first), a z ≠ z := by
  have hPC : ctx.second ≤ centralizer ({(z : G)} : Set G) :=
    ctx.second_le_residual_normalizer.trans
      (normalizer_le_centralizer_of_characteristic_involution
        ctx.firstResidual (center ctx.firstResidual) z hz
        (ctx.first_residual_center_eq_omegaOneCenter.trans hgen.symm))
  have hm : ∃ g ∈ ctx.first, g * (z : G) * g⁻¹ ≠ (z : G) := by
    by_contra hn
    push Not at hn
    let Z := zpowers (z : G)
    let L := ctx.first ⊔ ctx.second
    have hfirst : ctx.first ≤ centralizer ({(z : G)} : Set G) := by
      intro g hg
      exact mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp (hn g hg))
    have hLC : L ≤ centralizer (Z : Set G) := by
      rw [show centralizer (Z : Set G) = centralizer ({(z : G)} : Set G) from by
        change centralizer (zpowers (z : G) : Set G) = _
        rw [zpowers_eq_closure, centralizer_closure]]
      exact sup_le hfirst hPC
    have hZL : Z ≤ L := (zpowers_le.mpr (twoCoreIn_le ctx.first z.property)).trans le_sup_left
    have hnormal : (Z.subgroupOf L).Normal :=
      normal_subgroupOf_of_le_normalizer (hLC.trans (Subgroup.centralizer_le_normalizer _))
    have hZp : IsPGroup 2 Z := by
      apply IsPGroup.of_card (n := 1)
      change Nat.card (zpowers (z : G)) = 2 ^ 1
      simpa only [Nat.card_zpowers, pow_one] using hz
    have hzp : IsPGroup 2 (Z.subgroupOf L) :=
      hZp.of_equiv (subgroupOfEquivOfLe hZL).symm
    have hcore : Z ≤ twoCoreIn L := by
      rw [← map_subgroupOf_eq_of_le hZL]
      exact map_mono (show Z.subgroupOf L ≤ pCore 2 L from le_sSup ⟨hnormal, hzp⟩)
    have hzbot := hcore (mem_zpowers (z : G))
    rw [ctx.terminal.hypothesisTwo.fiveOne.join_twoCore_eq_bot, mem_bot] at hzbot
    rw [hzbot, orderOf_one] at hz
    omega
  obtain ⟨g, hg, hm⟩ := hm
  have hgN : g ∈ normalizer (twoCoreIn ctx.first : Set G) :=
    ((normal_subgroupOf_iff_le_normalizer (twoCoreIn_le ctx.first)).mp
      (twoCoreIn_normal ctx.first)) hg
  refine ⟨(twoCoreIn ctx.first).normalizerMonoidHom ⟨g, hgN⟩, ?_⟩
  intro he
  exact hm (congrArg (fun q : twoCoreIn ctx.first => (q : G)) he)

/-- A group whose automorphisms fix the marked involution cannot model the
actual first core with that marking. This is the final geometric contradiction
for an independently proved comparison-model calculation. -/
public theorem LargeTerminalContext.first_core_not_equiv_fixed_involution
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (z : twoCoreIn ctx.first)
    (hz : orderOf (z : G) = 2)
    (hgen : zpowers (z : G) = omegaOneCenter (S : Subgroup G))
    {H : Type*} [Group H] (w : H) (hfix : ∀ a : MulAut H, a w = w) :
    ¬ ∃ e : twoCoreIn ctx.first ≃* H, e z = w := by
  rintro ⟨e, he⟩
  obtain ⟨a, ha⟩ := ctx.first_core_aut_moves_central_involution z hz hgen
  have h := hfix ((MulAut.congr e) a)
  change e (a (e.symm w)) = w at h
  rw [← he, e.symm_apply_apply] at h
  exact ha (e.injective h)

end Stellmacher.Recognition
