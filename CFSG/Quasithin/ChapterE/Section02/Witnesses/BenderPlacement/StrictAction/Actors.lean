module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.StrictAction.Geometry
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.LinearEquality.Strict
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.ClassicalCubic
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.StrictAction

/-!
# The original strict cubic actor in every normalizing overgroup

The dihedral, binary linear, and Suzuki model estimates apply to the
same marked two-conjugate pair. Its Sylow inclusion transports the
actor into any normalizing overgroup containing the original Sylow.
The original quotient map is retained, together with its exact actor
kernel, nonzero elementary range, cubicity and strict fixed-space bound.

Source: Aschbacher–Smith E.2.13–15, printed pp.224–228. The pair group
itself is never assumed to normalize the original module.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
open TwoConjugate
variable {I D Q : Type*} [Group I] [Finite I] [Group D] [Finite D]
  [Group Q] [Finite Q] [IsElementaryAbelian 2 Q]
  {T : Sylow 2 I} {V M : Subgroup I} {g : I}

theorem QuotientModel.actor_strict {d : ℕ} (model : QuotientModel M d)
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting I = pCore 2 I)
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : I) =
        (a : I) * v * (a : I)⁻¹) :
    f.ker = (Z V g).subgroupOf (A V M g) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range < 2 * rank f.range ∧
      actionRatio ρ f.range < 2 ∧ cubicRatio ρ < 2 := by
  cases model with
  | dihedral hd p a hp hp2 ha' ξ =>
    exact h.dihedral_cubic_actor_strict hproper hfit
      (dihedral_star_card h hproper hp hp2 ξ) e ρ hρ f ha
  | linear hd ξ hb =>
    obtain ⟨S,hTS,hMS⟩ := linear_sylow_borel h ξ hb
    exact h.linear_two_cubic_actor_strict_of_TI hproper hfit d (by omega)
      (GaloisField.card 2 d (by omega)) ξ hTI S hTS hMS e ρ hρ f ha
  | suzuki m hm hd ξ hb =>
    exact h.suzuki_cubic_actor_strict hproper hfit m (by omega) ξ e ρ hρ f ha

variable {H : Type*} [Group H] [Finite H]
  {S : Sylow 2 H} {N W U : Subgroup H} [IsElementaryAbelian 2 W]
  {n : ℕ}

theorem OriginalWitness.actor_strict (w : OriginalWitness S N W n)
    (hWS : W ≤ (S : Subgroup H))
    (hSW : (S : Subgroup H) ≤ normalizer (W : Set H))
    (hcore : W ≤ N.pCoreIn 2) (hn : normalizer (W : Set H) ≤ N)
    (hfit : generalizedFitting H = pCore 2 H)
    (hTI : ∀ x ∈ N, W ⊓ W.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      W.map (MulAut.conj x).toMonoidHom = W)
    (hSU : (S : Subgroup H) ≤ U) (hU : U ≤ normalizer (W : Set H))
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (W : Set H)).subgroupOf U) :
    let h := w.pair.hypotheses hWS hSW hcore hn
    let ρ := DihedralCubic.representation U W hU q hq hk
    let f := DihedralCubic.actorMap h (w.pair.sylow_eq.le.trans (inf_le_left.trans hSU)) q
    f.ker = (Z (W.subgroupOf w.pair.subgroup) w.pair.conjugator).subgroupOf
        (A (W.subgroupOf w.pair.subgroup) (N.subgroupOf w.pair.subgroup) w.pair.conjugator) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range < 2 * rank f.range ∧
      actionRatio ρ f.range < 2 ∧ cubicRatio ρ < 2 := by
  let h := w.pair.hypotheses hWS hSW hcore hn
  let hSU' := w.pair.sylow_eq.le.trans (inf_le_left.trans hSU)
  let e := subgroupOfEquivOfLe w.pair.le
  let ρ := DihedralCubic.representation U W hU q hq hk
  let f := DihedralCubic.actorMap h hSU' q
  apply w.model.actor_strict h (w.pair.proper_of_quotient_card_ne_one hn w.model.card_ne_one)
    (w.pair.fitting hSW hfit) (restrict_TI w.pair.le hTI) e ρ
    (DihedralCubic.representation_injective U W hU q hq hk) f
  intro a v
  apply Subtype.ext
  change ((ρ (q (DihedralCubic.actorIn h hSU' a)) (Additive.ofMul (e v))).toMul : H) =
    ((a : w.pair.subgroup) : H) * ((v : w.pair.subgroup) : H) *
      ((a : w.pair.subgroup) : H)⁻¹
  rw [DihedralCubic.representation_apply]
  rfl

theorem OriginalWitness.cubicRatio_lt_two (w : OriginalWitness S N W n)
    (hWS : W ≤ (S : Subgroup H))
    (hSW : (S : Subgroup H) ≤ normalizer (W : Set H))
    (hcore : W ≤ N.pCoreIn 2) (hn : normalizer (W : Set H) ≤ N)
    (hfit : generalizedFitting H = pCore 2 H)
    (hTI : ∀ x ∈ N, W ⊓ W.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      W.map (MulAut.conj x).toMonoidHom = W)
    (hSU : (S : Subgroup H) ≤ U) (hU : U ≤ normalizer (W : Set H)) :
    cubicRatio (DihedralCubic.canonicalAction U W hU) < 2 := by
  let := DihedralCubic.centralizer_normal U W hU
  exact (w.actor_strict hWS hSW hcore hn hfit hTI hSU hU
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)).2.2.2.2.2
end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
