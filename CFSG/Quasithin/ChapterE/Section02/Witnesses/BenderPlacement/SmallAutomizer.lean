module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.SmallStar
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.SmallCoreAction
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.StrictAction.Geometry

/-!
# The original E.2.17 witness with its small quaternion core

The source degree bounds discharge the order-two star-image premise for
all stored original dihedral, linear and Suzuki witnesses on a four-space.
The same literal normalizer quotient then gives the quaternion central
product core, the order-six quotient and its full action on V. No model
choice, actor-dimension estimate or star-image order remains to be supplied
for the selected original witness.

The final conditional commutator retains precisely the global normalization
needed in the next part of E.2.17. The chosen subgroup W remains explicit.
Source: Aschbacher–Smith E.2.17 and 15.1.11, pp.229 and1085.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
open TwoConjugate
variable {I D Q : Type*} [Group I] [Finite I] [Group D] [Finite D]
  [Group Q] [Finite Q] [IsElementaryAbelian 2 Q]
  {T : Sylow 2 I} {V M : Subgroup I} {g : I}

theorem QuotientModel.star_card_two {d : ℕ} (model : QuotientModel M d)
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting I = pCore 2 I) (hV : Nat.card V = 16)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : I) =
        (a : I) * v * (a : I)⁻¹)
    (hD : Nat.card D ≤ 4) (hq : 1 < cubicRatio ρ) :
    Nat.card (V.map (QuotientGroup.mk' (J M))) = 2 := by
  cases model with
  | dihedral hd p a hp hp2 ha' ξ =>
    exact dihedral_star_card h hproper hp hp2 ξ
  | linear hd ξ hb =>
    exact h.star_card_two_of_small_automizer hproper hfit hV e ρ hρ f ha hD hq d
      (h.star_card_le_linear_two d (GaloisField.card 2 d (by omega)) ξ)
      (h.actor_rank_ge_linear_two_star hproper hfit d (by omega)
        (GaloisField.card 2 d (by omega)) ξ)
  | suzuki m hm hd ξ hb =>
    apply h.star_card_two_of_small_automizer hproper hfit hV e ρ hρ f ha hD hq (2*m+1)
      (h.star_card_le_suzuki m hm ξ)
    have hr := h.actor_rank_ge_suzuki hfit m (by omega) ξ
    omega

variable {H : Type*} [Group H] [Finite H]
  {S : Sylow 2 H} {N W U : Subgroup H} [IsElementaryAbelian 2 W] {n : ℕ}

theorem OriginalWitness.small_quaternion_core (w : OriginalWitness S N W n)
    (hWS : W ≤ (S : Subgroup H))
    (hSW : (S : Subgroup H) ≤ normalizer (W : Set H))
    (hcore : W ≤ N.pCoreIn 2) (hn : normalizer (W : Set H) ≤ N)
    (hfit : generalizedFitting H = pCore 2 H) (hW : Nat.card W = 16)
    (hSU : (S : Subgroup H) ≤ U) (hU : U ≤ normalizer (W : Set H))
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (W : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U W hU q hq hk)) :
    Nonempty (QuaternionCentralProductData (w.pair.subgroup.pCoreIn 2)) ∧
      U = w.pair.subgroup.pCoreIn 2 ⊔ (U ⊓ centralizer (W : Set H)) ∧
      w.pair.subgroup.pCoreIn 2 ⊓ centralizer (W : Set H) =
        w.pair.subgroup.pCoreIn 2 ⊓ W ∧
      Nonempty ((w.pair.subgroup ⧸ pCore 2 w.pair.subgroup) ≃* DihedralGroup 3) ∧
      (U ≤ normalizer (w.pair.subgroup.pCoreIn 2 : Set H) →
        ⁅U ⊓ centralizer (W : Set H), w.pair.subgroup.pCoreIn 2⁆ ≤
          w.pair.subgroup.pCoreIn 2 ⊓ W) := by
  let h := w.pair.hypotheses hWS hSW hcore hn
  let hSU' := w.pair.sylow_eq.le.trans (inf_le_left.trans hSU)
  let e := subgroupOfEquivOfLe w.pair.le
  let ρ := DihedralCubic.representation U W hU q hq hk
  let f := DihedralCubic.actorMap h hSU' q
  have hp := w.pair.proper_of_quotient_card_ne_one hn w.model.card_ne_one
  have hf := w.pair.fitting hSW hfit
  have hcard : Nat.card ((W.subgroupOf w.pair.subgroup).map
      (QuotientGroup.mk' (J (N.subgroupOf w.pair.subgroup)))) = 2 := by
    apply w.model.star_card_two h hp hf ((Nat.card_congr e.toEquiv).trans hW) e ρ
      (DihedralCubic.representation_injective U W hU q hq hk) f ?_ hD hratio
    intro a v
    apply Subtype.ext
    change ((ρ (q (DihedralCubic.actorIn h hSU' a)) (Additive.ofMul (e v))).toMul : H) =
      ((a : w.pair.subgroup) : H) * ((v : w.pair.subgroup) : H) *
        ((a : w.pair.subgroup) : H)⁻¹
    rw [DihedralCubic.representation_apply]
    rfl
  have hc := DihedralCubic.ambient_small_quaternion_core w.pair.le hU h hSU' hp hf
    hcard hW q hq hk hD hratio
  exact ⟨hc.1, hc.2.1, hc.2.2.1,
    DihedralCubic.ambient_small_dihedral_quotient w.pair.le hU h hSU' hp hf
      hcard hW q hq hk hD hratio, hc.2.2.2⟩
end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
