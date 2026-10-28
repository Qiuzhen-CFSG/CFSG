module
public import Theory.GroupAction.ExtraspecialInversionAutomorphisms
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration

/-!
# The faithful marked complement action in the U₄(3) normalizer

The actual complement K acts faithfully on D/Z(D). Its central involution
inverts that quotient; centralizing the involution removes the entire inner
automorphism kernel. The rotation acts nontrivially on the center W, and the
kernel of the center action is precisely the original SL₂(3) subgroup J.
These facts distinguish the required nontrivial similitude action from
order48 quaternion-Sylow subgroups contained in the symplectic group.

This supplies the action hypotheses at the start of Aschbacher,
*Sporadic Groups* (1994), 45.11, p.248, using the original 45.8 configuration.
It does not assert the remaining conjugacy classification in GSp₄(3).
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
  {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)

omit [Finite G] in
theorem involution_mem_complement : z ∈ c.K := by
  have hr := c.K.pow_mem (mem_sup_right (mem_zpowers (c.marking.s*c.marking.t))) 2
  simpa only [c.marking.rotation_square] using hr

omit [Finite G] in
theorem complement_normalizes_odd : c.K ≤ normalizer (c.D : Set G) :=
  (c.complement_le.trans inf_le_right).trans (CubicLine.normalizer_normalizes_oddKernel c.W)

omit [Finite G] in
theorem odd_center : center c.D = c.W.subgroupOf c.D := by
  ext x
  constructor
  · intro hx
    have hx' : (x:G) ∈ Subgroup.centralizer (c.D : Set G) := by
      intro y hy
      exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
    exact c.odd_centralizer ▸ hx'
  · intro hx
    have hx' : (x:G) ∈ Subgroup.centralizer (c.D : Set G) := c.odd_centralizer ▸ hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hx' y y.property)

noncomputable def complementAction : c.K →* MulAut c.D :=
  c.D.normalizerMonoidHom.comp (inclusion c.complement_normalizes_odd)

omit [Finite G] in
@[simp] theorem complementAction_apply (k : c.K) (d : c.D) :
    (c.complementAction k d : G) = (k:G) * (d:G) * (k:G)⁻¹ := rfl

noncomputable def involutionAction : MulAut c.D :=
  c.complementAction ⟨z,c.involution_mem_complement⟩

noncomputable def complementQuotientAction : c.K →* MulAut (c.D ⧸ center c.D) :=
  (quotientAut (center c.D)).comp c.complementAction

omit [Finite G] in
theorem involutionAction_inverts (d : c.D) :
    quotientAut (center c.D) c.involutionAction (QuotientGroup.mk' (center c.D) d) =
      (QuotientGroup.mk' (center c.D) d)⁻¹ := by
  rw [quotientAut_apply_mk]
  apply eq_inv_of_mul_eq_one_left
  rw [←map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  rw [c.odd_center]
  exact c.odd_inversion d d.property

omit [Finite G] in
theorem complementAction_commute_involution (k : c.K) :
    Commute c.involutionAction (c.complementAction k) := by
  have hh : Commute (⟨z,c.involution_mem_complement⟩ : c.K) k := by
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp (c.complement_le k.property).1).symm
  exact hh.map c.complementAction

theorem complementQuotientAction_injective : Function.Injective c.complementQuotientAction := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro k hk
  let : IsExtraspecial 3 c.D := c.odd_extraspecial
  have ha : c.complementAction k = 1 :=
    IsExtraspecial.aut_eq_one_of_quotient_eq_one_of_commute_inversion
      c.involutionAction (c.complementAction k) c.involutionAction_inverts hk
      (c.complementAction_commute_involution k)
  have hkC : (k:G) ∈ Subgroup.centralizer (c.D : Set G) := by
    intro d hd
    have hh := congrArg Subtype.val (DFunLike.congr_fun ha (⟨d,hd⟩ : c.D))
    change (k:G) * d * (k:G)⁻¹ = d at hh
    have he := congrArg (fun a => a * (k:G)) hh
    simpa only [mul_assoc,inv_mul_cancel, mul_one] using he.symm
  have hkW : (k:G) ∈ c.W := c.odd_centralizer ▸ hkC
  have hkD : (k:G) ∈ c.D := CubicLine.le_oddKernel c.W c.line_card hkW
  apply Subtype.ext
  exact mem_bot.mp (c.complement_disjoint.eq_bot ▸ show (k:G) ∈ c.D ⊓ c.K from ⟨hkD,k.property⟩)
omit [Finite G] in
theorem rotation_inverts_line (w : G) (hw : w ∈ c.W) :
    (c.marking.s*c.marking.t)*w*(c.marking.s*c.marking.t)⁻¹ = w⁻¹ := by
  apply c.marking.rotation_inverts
  rw [←c.actors_eq]
  exact (zpowers_le.mpr c.actors.x.property) hw

omit [Finite G] in
theorem rotation_not_centralizes_line :
    c.marking.s*c.marking.t ∉ Subgroup.centralizer (c.W : Set G) := by
  intro hr
  have he := c.rotation_inverts_line c.actors.x (mem_zpowers _)
  have hc := hr c.actors.x (mem_zpowers _)
  rw [←hc,mul_inv_cancel_right] at he
  have htwo : (c.actors.x:G)^2 = 1 := by
    rw [pow_two]
    calc (c.actors.x:G)*(c.actors.x:G) = (c.actors.x:G)⁻¹*(c.actors.x:G) :=
           congrArg (·*(c.actors.x:G)) he
         _ = 1 := inv_mul_cancel _
  have hd := orderOf_dvd_of_pow_eq_one htwo
  rw [c.actors.x_order] at hd
  norm_num at hd

omit [Finite G] in
theorem special_centralizes_line : c.J ≤ Subgroup.centralizer (c.W : Set G) := by
  apply sup_le
  · exact le_centralizer_iff.mp (zpowers_le.mpr c.actors.x_centralizes)
  · rw [le_centralizer_iff,zpowers_le]
    intro y hy
    exact mem_centralizer_singleton_iff.mp
      ((zpowers_le.mpr (mem_centralizer_singleton_iff.mpr c.actors.commute.symm.eq)) hy)

omit [Finite G] in
/-- The SL₂(3) subgroup is precisely the kernel of the actual center action. -/
theorem complement_centralizer_line :
    c.K ⊓ Subgroup.centralizer (c.W : Set G) = c.J := by
  let L := c.K ⊓ Subgroup.centralizer (c.W : Set G)
  have hJL : c.J ≤ L := le_inf le_sup_left c.special_centralizes_line
  have hLK : L ≤ c.K := inf_le_left
  have hJK : c.J ≤ c.K := le_sup_left
  have hjcard : Nat.card (c.J.subgroupOf c.K) = 24 :=
    (Nat.card_congr (subgroupOfEquivOfLe hJK).toEquiv).trans c.special_card
  have hjindex : c.J.relIndex c.K = 2 := by
    have hh := (c.J.subgroupOf c.K).card_mul_index
    rw [hjcard,c.complement_card] at hh
    change 24*c.J.relIndex c.K=48 at hh
    omega
  have hmul := relIndex_mul_relIndex c.J L c.K hJL hLK
  rw [hjindex] at hmul
  have hLne : L.relIndex c.K ≠ 1 := by
    intro hL
    have hKL : c.K ≤ L := relIndex_eq_one.mp hL
    exact c.rotation_not_centralizes_line
      (hKL (mem_sup_right (mem_zpowers _))).2
  have hJone : c.J.relIndex L = 1 := by
    have hd : L.relIndex c.K ∣ 2 := ⟨c.J.relIndex L,by simpa [Nat.mul_comm] using hmul.symm⟩
    have he := (Nat.dvd_prime Nat.prime_two).mp hd
    have heq : L.relIndex c.K=2 := he.resolve_left hLne
    rw [heq] at hmul
    omega
  exact le_antisymm (relIndex_eq_one.mp hJone) hJL

/-- The original faithful quotient image has order48. -/
theorem complementQuotientAction_range_card :
    Nat.card c.complementQuotientAction.range = 48 := by
  rw [←Nat.card_congr (MonoidHom.ofInjective c.complementQuotientAction_injective).toEquiv]
  exact c.complement_card

omit [Finite G] in
/-- The central quotient is the original ternary space of order81. -/
theorem odd_central_quotient_card : Nat.card (c.D ⧸ center c.D) = 81 := by
  let : IsExtraspecial 3 c.D := c.odd_extraspecial
  have hh := card_eq_card_quotient_mul_card_subgroup (center c.D)
  rw [c.odd_card,IsExtraspecial.center_order_p 3 c.D] at hh
  omega
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
