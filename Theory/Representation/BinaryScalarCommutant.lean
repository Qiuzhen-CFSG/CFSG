module
public import Theory.Representation.BinaryOffender.NormalizerRank
public import Theory.Representation.BinaryOffender.PerfectNormalizer
public import Mathlib.GroupTheory.IsPerfect
public import Theory.GroupTheory.QuasithinBasic

/-!
# Binary actions with scalar commutant

In characteristic two, a scalar involution is identity. Elementary subgroups
of the full linear normalizer therefore embed in the automorphism group of
the faithfully marked actor. A perfect commuting action is trivial because
its scalar image is abelian. These statements retain the full normalizer
and require no irreducibility premise.

Source application: the orthogonal and Suzuki rows in Aschbacher--Smith
10.1.1 and 10.2.12, printed pp.741,754.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Representation.BinaryScalarCommutant
variable {F J V : Type*} [Field F] [CharP F 2] [Group J]
  [AddCommGroup V] [Module (ZMod 2) V] [Module F V] [Nontrivial V]
  (σ : Representation (ZMod 2) J V)
  (hs : ∀ f : V →ₗ[ZMod 2] V, (∀ j v, f (σ j v) = σ j (f v)) →
    ∃ c : F, ∀ v, f v = c • v)

include hs
theorem commuting_involution_eq_one (f : V →ₗ[ZMod 2] V)
    (hf : ∀ j v, f (σ j v) = σ j (f v)) (h2 : f * f = 1) : f = 1 := by
  obtain ⟨c,hc⟩ := hs f hf
  obtain ⟨v,hv⟩ := exists_ne (0 : V)
  have hc2 : c*c = 1 := by
    apply (smul_left_injective F hv)
    change (c*c) • v = (1 : F) • v
    rw [mul_smul,←hc,←hc]
    simpa only [Module.End.mul_apply,one_smul,Module.End.one_apply] using
      LinearMap.congr_fun h2 v
  have hc1 : c = 1 := CharTwo.sq_injective (by simpa only [pow_two,one_mul] using hc2)
  ext w
  simp only [hc,hc1,one_smul,Module.End.one_apply]

theorem normalizer_rank_le [Finite V] (hfaith : Function.Injective σ) :
    primeRank 2 (BinaryOffender.linearNormalizer σ) ≤ primeRank 2 (MulAut J) := by
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let : Finite J := Finite.of_injective σ hfaith
  let e := BinaryOffender.PerfectNormalizer.imageEquiv σ hfaith
  rw [primeRank_equiv 2 (MulAut.congr e)]
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro A hA
  let := hA
  let f := (BinaryOffender.actionImage σ).normalizerMonoidHom.comp A.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro a ha
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    apply commuting_involution_eq_one σ hs
    · intro j v
      change (a : BinaryOffender.linearNormalizer σ) ∈
        (BinaryOffender.actionImage σ).normalizerMonoidHom.ker at ha
      rw [normalizerMonoidHom_ker] at ha
      exact (congrArg (fun z : (Module.End (ZMod 2) V)ˣ => z.val v)
        (ha (σ.asGroupHom j) ⟨j,rfl⟩)).symm
    · have h2 : (a : BinaryOffender.linearNormalizer σ)^2=1 :=
        elemPow_eq_one_of_isElementaryAbelian (a : BinaryOffender.linearNormalizer σ) a.property
      exact congrArg (fun z : BinaryOffender.linearNormalizer σ => z.val.val) h2
  have he : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).le.trans
    ((primeRank_le_iff_elementary_card_le _).mp le_rfl f.range he)

omit [CharP F 2] [Nontrivial V] in
theorem perfect_commuting_action_trivial {Q : Type*} [Group Q] [Group.IsPerfect Q]
    (η : Representation (ZMod 2) Q V)
    (hcomm : ∀ q j v, η q (σ j v) = σ j (η q v)) :
    ∀ q v, η q v = v := by
  let R := η.asGroupHom.range
  let : Group.IsPerfect R := Group.IsPerfect.range η.asGroupHom
  let : IsMulCommutative R := ⟨⟨by
    intro a b
    obtain ⟨x,hx⟩ := a.property
    obtain ⟨y,hy⟩ := b.property
    apply Subtype.ext
    change a.val * b.val = b.val * a.val
    rw [←hx,←hy]
    apply Units.ext
    apply LinearMap.ext
    intro v
    obtain ⟨c,hc⟩ := hs (η x) (hcomm x)
    obtain ⟨d,hd⟩ := hs (η y) (hcomm y)
    change η x (η y v) = η y (η x v)
    rw [hc,hd,hc,hd,smul_comm]⟩⟩
  intro q v
  have hh := congrArg (fun a : R => a.val.val v)
    (Subsingleton.elim (η.asGroupHom.rangeRestrict q) 1)
  exact hh
end Representation.BinaryScalarCommutant
