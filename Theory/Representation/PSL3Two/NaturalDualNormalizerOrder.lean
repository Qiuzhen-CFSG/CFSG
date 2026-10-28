module
public import Theory.Representation.PSL3Two.NaturalDualNormalizerMarking
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.Representation.BinaryGroupAction
public import Theory.ElementaryAbelian.Quotient

/-!
# The order obstruction for a normal natural-plus-dual action

A group normalizing both a marked natural-plus-dual six-space and its
surjective binary-three actor acts on SL3(2) by automorphisms. If the
six-space centralizer is a two-group, the resulting kernel is a two-group;
therefore the ambient normalizer order is not divisible by nine. The full
mapped actor is retained, with no injectivity assumption on it.

Source: Aschbacher--Smith 4.4.12, pp.621--622, in the literal doubled-binary
ordinary module application. The proof isolates the normalizer-order step
from the earlier maximal-parabolic consumer.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative
namespace BinaryLinearThree.NaturalDual

private theorem not_nine {P : Type*} [_root_.Group P] [Finite P]
    (η : Representation (ZMod 2) P NaturalDual.Space)
    (B : Subgroup P) [B.Normal]
    (q : B →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (he : ∀ b : B, η b = NaturalDual.action (q b))
    (hk : IsPGroup 2 η.ker) : ¬ 9 ∣ Nat.card P := by
  obtain ⟨a,ha,hker⟩ := NaturalDual.exists_automorphism_marking η B q hq he
  have hka : a.ker = η.ker := by ext x; exact hker x
  have hkr : IsPGroup 2 a.ker := hka.symm ▸ hk
  obtain ⟨n,hn⟩ := hkr.exists_card_eq
  have hc := a.ker.card_mul_index
  rw [index_ker,hn] at hc
  intro hd
  have hr : 9 ∣ Nat.card a.range :=
    ((by decide : Nat.Coprime 9 2).pow_right n).dvd_of_dvd_mul_left (hc.symm ▸ hd)
  have h9 := hr.trans a.range.card_subgroup_dvd_card
  rw [Nat.card_congr (MulAut.congr Matrix.PSL3Two.equiv).toEquiv,
    Matrix.PSL3Two.Automorphisms.card_aut] at h9
  norm_num at h9

private theorem not_nine_normal {P : Type*} [_root_.Group P] [Finite P]
    (U B : Subgroup P) [IsElementaryAbelian 2 U] [U.Normal] [B.Normal]
    (q : B →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (e : Additive U ≃ₗ[ZMod 2] NaturalDual.Space)
    (he : ∀ b : B, ∀ v : U,
      e (Additive.ofMul (MulAut.conjNormal b.val v)) =
        NaturalDual.action (q b) (e (Additive.ofMul v)))
    (hc : IsPGroup 2 (centralizer (U : Set P))) : ¬ 9 ∣ Nat.card P := by
  let ρ := elementaryRepresentation (p:=2) (MulAut.conjNormal : P →* MulAut U)
  let η : Representation (ZMod 2) P NaturalDual.Space := {
    toFun p := e.toLinearMap.comp ((ρ p).comp e.symm.toLinearMap)
    map_one' := by
      apply LinearMap.ext
      intro v
      change e (ρ 1 (e.symm v)) = v
      rw [map_one]
      exact e.apply_symm_apply v
    map_mul' p r := by
      apply LinearMap.ext
      intro v
      change e (ρ (p*r) (e.symm v)) = e (ρ p (e.symm (e (ρ r (e.symm v)))))
      rw [e.symm_apply_apply,map_mul]; rfl }
  have hk : η.ker ≤ centralizer (U : Set P) := by
    intro p hp
    apply mem_centralizer_iff.mpr
    intro v hv
    have hh := LinearMap.congr_fun hp (e (Additive.ofMul (⟨v,hv⟩ : U)))
    change e (ρ p (e.symm (e (Additive.ofMul (⟨v,hv⟩ : U))))) =
      e (Additive.ofMul (⟨v,hv⟩ : U)) at hh
    rw [e.symm_apply_apply] at hh
    have hh' := congrArg (fun x : Additive U => (x.toMul : P)) (e.injective hh)
    change p * v * p⁻¹ = v at hh'
    exact (mul_inv_eq_iff_eq_mul.mp hh').symm
  apply not_nine η B q hq _ (hc.to_le hk)
  intro b
  apply LinearMap.ext
  intro v
  change e (ρ b.val (e.symm v)) = NaturalDual.action (q b) v
  rw [show ρ b.val (e.symm v) = Additive.ofMul (MulAut.conjNormal b.val (e.symm v).toMul) from rfl,
    he]
  exact congrArg (NaturalDual.action (q b)) (e.apply_symm_apply v)

private def linearize {U V : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup V] [Module (ZMod 2) V]
    (e : Multiplicative U ≃* Multiplicative V) : U ≃ₗ[ZMod 2] V :=
  let a : U ≃+ V := {
    toFun v := (e (Multiplicative.ofAdd v)).toAdd
    invFun v := (e.symm (Multiplicative.ofAdd v)).toAdd
    left_inv v := e.symm_apply_apply v
    right_inv v := e.apply_symm_apply v
    map_add' v w := congrArg Multiplicative.toAdd (e.map_mul
      (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  { a with map_smul' := ZMod.map_smul a }

/-- A normal marked natural-plus-dual actor with a two-group centralizer
forces the containing normalizer to have order prime to nine. -/
theorem not_nine_mapped_conjugation
    {R Q : Type*} [_root_.Group R] [_root_.Group Q] [Finite Q]
    (f : R →* Q) (q : R →* BinaryLinearThree.Group) (hq : Function.Surjective q)
    (u : Multiplicative Space →* Q) (hu : Function.Injective u)
    (ha : ∀ r v, f r * u (Multiplicative.ofAdd v) * (f r)⁻¹ =
      u (Multiplicative.ofAdd (action (q r) v)))
    (P : Subgroup Q) (hfP : f.range ≤ P) (hEP : u.range ≤ P)
    (hB : (f.range.subgroupOf P).Normal) (hU : (u.range.subgroupOf P).Normal)
    (hc : IsPGroup 2 (centralizer (u.range : Set Q))) : ¬ 9 ∣ Nat.card P := by
  let : IsElementaryAbelian 2 (Multiplicative Space) :=
    Representation.BinaryGroupAction.elementary
  let : IsElementaryAbelian 2 u.range := IsElementaryAbelian.of_surjective
    u.rangeRestrict u.rangeRestrict_surjective
  let B := f.range.subgroupOf P
  let U := u.range.subgroupOf P
  let := hB
  let := hU
  let eB : B ≃* f.range := subgroupOfEquivOfLe hfP
  let eU : U ≃* u.range := subgroupOfEquivOfLe hEP
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_surjective eU.symm.toMonoidHom eU.symm.surjective
  have hk : f.rangeRestrict.ker ≤ q.ker := by
    intro r hr
    have hfr : f r = 1 := congrArg Subtype.val hr
    apply NaturalDual.action_injective
    apply LinearMap.ext
    intro v
    have he := ha r v
    rw [hfr,one_mul,inv_one,mul_one] at he
    have hh := congrArg Multiplicative.toAdd (hu he)
    change v = NaturalDual.action (q r) v at hh
    simpa only [map_one,Module.End.one_apply] using hh.symm
  let qB : f.range →* BinaryLinearThree.Group :=
    f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨q,hk⟩
  have hqB : Function.Surjective qB := by
    intro g
    obtain ⟨r,rfl⟩ := hq g
    exact ⟨f.rangeRestrict r,by simp [qB]⟩
  let v : Multiplicative NaturalDual.Space ≃* U := (MonoidHom.ofInjective hu).trans eU.symm
  let c := linearize ((MulEquiv.toMultiplicative_toAdditive :
    Multiplicative (Additive U) ≃* U).trans v.symm)
  have hcU : IsPGroup 2 (centralizer (U : Set P)) := by
    apply hc.comap_subtype.to_le
    intro x hx y hy
    exact congrArg P.subtype (hx ⟨y,hEP hy⟩ hy)
  apply not_nine_normal U B (qB.comp eB.toMonoidHom)
    (hqB.comp eB.surjective) c _ hcU
  intro r x
  obtain ⟨s,hs⟩ := f.rangeRestrict_surjective (eB r)
  obtain ⟨w,rfl⟩ := v.surjective x
  have hqr : qB (eB r) = q s := by rw [←hs]; simp [qB]
  have hfr : f s = r.val.val := congrArg Subtype.val hs
  have hc (z : Multiplicative NaturalDual.Space) : c (Additive.ofMul (v z)) = z.toAdd :=
    v.symm_apply_apply z
  have hact : MulAut.conjNormal r.val (v w) =
      v (Multiplicative.ofAdd (NaturalDual.action (q s) w.toAdd)) := by
    apply Subtype.ext
    apply Subtype.ext
    change r.val.val * u w * r.val.val⁻¹ = _
    rw [←hfr]
    exact ha s w.toAdd
  rw [hact,hc,hc]
  change _ = NaturalDual.action (qB (eB r)) w.toAdd
  rw [hqr]
  rfl

end BinaryLinearThree.NaturalDual
