module
public import Theory.SpecificGroups.PSL2.EightCentralCovers
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.GroupTheory.CentralPResidualCommutator
public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.Representation.ElementaryAbelianAction.Commutator
public import Theory.GroupTheory.Commutator.SimpleSubnormal
public import Theory.Representation.SL2.EightCentralizer
/-!
# The binary core action above PSL₂(8)

For a perfect group with two-core Q and quotient PSL₂(8), the trivial
universal-cover kernel gives [Q,H]=Q. If Q is extraspecial, its order-two
center is central in H. Perfectness eliminates every fixed vector on Q/Z(Q).
These statements use any literal surjective coordinates with kernel Z(Q)
and the corresponding conjugation square. At quotient order 256, the
binary degree and Schur-field argument makes the action centralizer trivial.

Source: Aschbacher--Smith 14.2.18, p.987. The actual first-parabolic action
is consumed by `Chapter14/Section02/EightLargeParabolic/CoreCentralizer`.
-/
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.SpecificGroups.PSL2Eight
variable {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]

omit [Finite H] in
theorem core_commutator_eq
    (e : (H ⧸ pCore 2 H) ≃* Theory.PSL2.BinaryGroup 3) :
    ⁅pCore 2 H, (⊤ : Subgroup H)⁆ = pCore 2 H := by
  let Q := pCore 2 H
  let D := ⁅Q, (⊤ : Subgroup H)⁆
  have hDQ : D ≤ Q := commutator_le_left Q ⊤
  let f := e.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective Q)
  have hk : f.ker = Q := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  let a := QuotientGroup.lift D f (hk.symm ▸ hDQ)
  have ha : Function.Surjective a := QuotientGroup.lift_surjective_of_surjective _ _ hf _
  have hac : a.ker ≤ center (H ⧸ D) := by
    intro x hx
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective D x
    have hg : g ∈ Q := hk ▸ hx
    rw [mem_center_iff]
    intro y
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective D y
    apply (commutatorElement_eq_one_iff_mul_comm.mp ?_).symm
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr
      (commutator_mem_commutator hg (mem_top h))
  let c : PerfectCentralCovering.Cover (H ⧸ D) (Theory.PSL2.BinaryGroup 3) :=
    { toMonoidHom := a
      surjective := ha
      isPerfect := inferInstance
      ker_le_center := hac }
  have hi := cover_injective c
  apply le_antisymm hDQ
  intro g hg
  apply (QuotientGroup.eq_one_iff g).mp
  apply hi
  change f g = a 1
  rw [map_one]
  exact (show g ∈ f.ker from hk.symm ▸ hg)

variable (Q : Subgroup H) [Q.Normal] [IsExtraspecial 2 Q]

def centerAction : H →* MulAut (Q ⧸ center Q) :=
  (quotientAut (center Q)).comp (MulAut.conjNormal : H →* MulAut Q)

include Q in
theorem centerAction_fixed
    (hz : (center Q).map Q.subtype ≤ center H)
    (v : Q ⧸ center Q) (hv : ∀ h, centerAction Q h v = v) : v = 1 := by
  obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective (center Q) v
  let Z := (center Q).map Q.subtype
  let : Group.IsPerfect (⊤ : Subgroup H) := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := H)).symm.toMonoidHom) topEquiv.symm.surjective
  have hZp : IsPGroup 2 (Z.subgroupOf (⊤ : Subgroup H)) :=
    ((IsExtraspecial.isPGroup 2 Q).to_subgroup (center Q)).map Q.subtype |>.comap_of_injective
      (⊤ : Subgroup H).subtype (⊤ : Subgroup H).subtype_injective
  have hZc : Z.subgroupOf (⊤ : Subgroup H) ≤ center (⊤ : Subgroup H) := by
    intro z hz'
    rw [mem_center_iff]
    intro h
    exact Subtype.ext (mem_center_iff.mp (hz hz') h)
  have hc := commute_of_central_p_commutator_of_isPPerfect
    (⊤ : Subgroup H) (Z.subgroupOf ⊤) (by
      intro N hN hquot
      let : N.Normal := hN
      let : Group.IsNilpotent ((⊤ : Subgroup H) ⧸ N) := hquot.isNilpotent
      by_contra hn
      let : Nontrivial ((⊤ : Subgroup H) ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
      exact Group.IsPerfect.not_isSolvable ((⊤ : Subgroup H) ⧸ N) inferInstance) hZp hZc (q : H) (by
      intro h
      have hh := hv h.val
      rw [centerAction, MonoidHom.comp_apply, quotientAut_apply_mk] at hh
      change QuotientGroup.mk' (center Q) (MulAut.conjNormal h.val q) =
        QuotientGroup.mk' (center Q) q at hh
      have hd : MulAut.conjNormal h.val q / q ∈ center Q :=
        (QuotientGroup.eq_iff_div_mem).mp hh
      rw [map_subgroupOf_eq_of_le (le_top : Z ≤ ⊤)]
      exact ⟨_,hd,by change ((MulAut.conjNormal h.val q / q : Q) : H) = _; simp only [div_eq_mul_inv, coe_mul, coe_inv, MulAut.conjNormal_apply, commutatorElement_def]⟩)
  apply (QuotientGroup.eq_one_iff q).mpr
  rw [mem_center_iff]
  intro x
  exact Subtype.ext (hc (x : H) (mem_top _)).eq.symm
end Theory.SpecificGroups.PSL2Eight

namespace Theory.SpecificGroups.PSL2Eight
open Representation
variable {H V : Type*} [Group H] [Finite H] [Group.IsPerfect H]
  [Group V] [Finite V] [IsElementaryAbelian 2 V]

def linearAction (a : H →* MulAut V) : Representation (ZMod 2) H (Additive V) where
  toFun h := (a h).toAdditive.toAddMonoidHom.toZModLinearMap 2
  map_one' := by ext v; exact congrArg (fun f : MulAut V => Additive.ofMul (f v.toMul)) a.map_one
  map_mul' h k := by
    ext v
    exact congrArg (fun f : MulAut V => Additive.ofMul (f v.toMul)) (a.map_mul h k)

variable (e : (H ⧸ pCore 2 H) ≃* Theory.PSL2.BinaryGroup 3)
    (c : pCore 2 H →* V) (hs : Function.Surjective c) (hk : c.ker = center (pCore 2 H))
    (a : H →* MulAut V)
    (ha : ∀ (h : H) (q : pCore 2 H), c (MulAut.conjNormal h q) = a h (c q))
include e hs hk ha

omit hk [Finite H] [Finite V] in
theorem linearAction_coinvariants : Coinvariants.ker (linearAction a) = ⊤ := by
  let Q := pCore 2 H
  let C : Subgroup Q :=
    ((Coinvariants.ker (linearAction a)).toAddSubgroup.toSubgroup').comap c
  have hQC : Q ≤ C.map Q.subtype := by
    change pCore 2 H ≤ C.map Q.subtype
    rw [←core_commutator_eq e, commutator_comm]
    apply commutator_le.mpr
    intro h _ q hq
    let q' : Q := ⟨q,hq⟩
    refine ⟨MulAut.conjNormal h q' / q',?_,?_⟩
    · change Additive.ofMul (c (MulAut.conjNormal h q' / q')) ∈ Coinvariants.ker (linearAction a)
      rw [map_div,ha]
      exact Coinvariants.sub_mem_ker (ρ := linearAction a) h (Additive.ofMul (c q'))
    · change ((MulAut.conjNormal h q' / q' : Q) : H) = _
      simp only [div_eq_mul_inv, coe_mul, coe_inv, MulAut.conjNormal_apply, commutatorElement_def]
      rfl
  apply top_unique
  intro v _
  obtain ⟨q,hq⟩ := hs v.toMul
  obtain ⟨w,hw,he⟩ := hQC q.property
  have hwq : w = q := Subtype.ext he
  subst w
  change Additive.ofMul (c q) ∈ Coinvariants.ker (linearAction a) at hw
  rw [hq] at hw
  exact hw

omit e [Finite V] in
theorem linearAction_invariants [IsExtraspecial 2 (pCore 2 H)]
    (hz : (center (pCore 2 H)).map (pCore 2 H).subtype ≤ center H) :
    (linearAction a).invariants = ⊥ := by
  let Q := pCore 2 H
  let f : (Q ⧸ center Q) ≃* V := QuotientGroup.liftEquiv (center Q) hs hk.symm
  have hf (q : Q) : f (QuotientGroup.mk' (center Q) q) = c q := rfl
  have he (h : H) (v : Q ⧸ center Q) : f (centerAction Q h v) = a h (f v) := by
    obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective (center Q) v
    rw [centerAction,MonoidHom.comp_apply,quotientAut_apply_mk,hf,hf,ha]
  apply bot_unique
  intro v hv
  change v = 0
  have hh : ∀ h, centerAction Q h (f.symm v.toMul) = f.symm v.toMul := by
    intro h
    apply f.injective
    rw [he,f.apply_symm_apply]
    exact congrArg Additive.toMul (hv h)
  have hzv := centerAction_fixed Q hz _ hh
  have := congrArg f hzv
  rw [f.apply_symm_apply,map_one] at this
  exact this
end Theory.SpecificGroups.PSL2Eight

namespace Theory.SpecificGroups.PSL2Eight
open Representation
variable {H V : Type*} [Group H] [Finite H] [Group.IsPerfect H]
  [Group V] [Finite V] [IsElementaryAbelian 2 V]

omit [Finite H] [Group.IsPerfect H] in
theorem extraspecial_center_central (Q : Subgroup H) [Q.Normal] [IsExtraspecial 2 Q] :
    (center Q).map Q.subtype ≤ center H := by
  rintro z ⟨w,hw,rfl⟩
  rw [mem_center_iff]
  intro h
  let α : MulAut (center Q) := centerCongr (MulAut.conjNormal h : MulAut Q)
  have he : α ⟨w,hw⟩ = ⟨w,hw⟩ := by
    by_cases hw1 : (⟨w,hw⟩ : center Q) = 1
    · rw [hw1,map_one]
    · obtain ⟨t,ht,hu⟩ := (Nat.card_eq_two_iff' (1 : center Q)).mp
        (IsExtraspecial.center_order_p 2 Q)
      exact (hu _ (fun hn => hw1 (α.injective (hn.trans (map_one α).symm)))).trans
        (hu _ hw1).symm
  have hv := congrArg (fun x : center Q => ((x : Q) : H)) he
  change h * (w : H) * h⁻¹ = w at hv
  exact (mul_inv_eq_iff_eq_mul).mp hv

theorem extraspecial_action_centralizer_eq_bot [IsExtraspecial 2 (pCore 2 H)]
    (e : (H ⧸ pCore 2 H) ≃* Theory.PSL2.BinaryGroup 3)
    (c : pCore 2 H →* V) (hs : Function.Surjective c) (hk : c.ker = center (pCore 2 H))
    (a : H →* MulAut V)
    (ha : ∀ (h : H) (q : pCore 2 H), c (MulAut.conjNormal h q) = a h (c q))
    (hcard : Nat.card V = 256) : centralizer (a.range : Set (MulAut V)) = ⊥ := by
  let ρ := linearAction a
  have hd : Module.finrank (ZMod 2) (Additive V) = 8 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod] at hc
    have h : 2 ^ Module.finrank (ZMod 2) (Additive V) = 2 ^ 8 := hc.symm.trans hcard
    exact Nat.pow_right_injective (by decide : 1 < 2) h
  have hf := linearAction_invariants c hs hk a ha (extraspecial_center_central (pCore 2 H))
  have hg := linearAction_coinvariants e c hs a ha
  apply bot_unique
  intro u hu
  change u = 1
  let b : Additive V ≃ₗ[ZMod 2] Additive V :=
    u.toAdditive.toLinearEquiv (fun c x => ZMod.map_smul u.toAdditive.toAddMonoidHom c x)
  have hb : b = 1 := Representation.SL2.eight_commuting_equiv_eq_one
    (e.trans (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm) ρ hd hf hg b (by
      intro h v
      exact congrArg (fun t : MulAut V => Additive.ofMul (t v.toMul))
        ((mem_centralizer_iff.mp hu) (a h) ⟨h,rfl⟩).symm)
  ext v
  exact congrArg (fun f : Additive V ≃ₗ[ZMod 2] Additive V => (f (Additive.ofMul v)).toMul) hb
end Theory.SpecificGroups.PSL2Eight
