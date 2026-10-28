module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Setup
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Fusion
public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.FieldTheory.Finiteness

/-!
# The faithful binary action of the HS normalizer quotient

Conjugation in M/E on Qbar factors through the actual quotient M/Q.
Linearizing gives its canonical binary representation. The equivalence
Q/Φ(Q) ≃ Qbar is linear and agrees with coreMap. Fixed vectors are precisely
the relative centralizer used by the involution-coset fusion theorem, and
a fixed vector which is a displacement lies in its literal commutator subgroup.

The actual cover core is self-centralizing, by surjectivity onto the model
core. Burnside's Frattini kernel theorem therefore proves faithfulness,
without an abelian-core or dimension hypothesis. Once |E| = 8 is established,
the core order 128 forces dimension four. Neither that order-eight premise
nor the nonsplitting and indecomposability claims is asserted here.

Source: Aschbacher–Smith I.2.2(5), printed p.412 / PDF p.423;
the fixed-point conclusion consumed from B.4.8(2), printed p.91.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
variable {K : Type*} [Group K]

/-- The embedded core projection uses exactly the quotient map by E. -/
theorem coreMap_val
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) (q : Q e) :
    (coreMap e q : M e ⧸ E e) = QuotientGroup.mk' (E e) (q : M e) := rfl

variable [Finite K]

/-- The source Frattini quotient has its canonical elementary abelian structure. -/
instance frattiniQuotient_elementary
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    IsElementaryAbelian 2 (Q e ⧸ frattini (Q e)) := by
  let : Fact (IsPGroup 2 (Q e)) := ⟨pCore_isPGroup⟩
  exact isElementaryAbelian_quotient_frattini

/-- The literal Q/Φ(Q) and its embedded image are the same binary vector space. -/
noncomputable def frattiniLinearEquiv
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    Additive (Q e ⧸ frattini (Q e)) ≃ₗ[ZMod 2] Additive (Qbar e) :=
  { (frattiniEquiv e).toAdditive with
    map_smul' := ZMod.map_smul (frattiniEquiv e).toAdditive }

theorem frattiniLinearEquiv_mk
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) (q : Q e) :
    frattiniLinearEquiv e (Additive.ofMul (QuotientGroup.mk' (frattini (Q e)) q)) =
      Additive.ofMul (coreMap e q) := rfl

/-- Q acts trivially on its elementary Frattini image in M/E. -/
theorem Q_le_frattini_conjugation_ker
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    Q e ≤ ((MulAut.conjNormal (H := Qbar e)).comp (QuotientGroup.mk' (E e))).ker := by
  intro q hq
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  change QuotientGroup.mk' (E e) q * (v : M e ⧸ E e) *
    (QuotientGroup.mk' (E e) q)⁻¹ = v
  have hc := congrArg Subtype.val (mul_comm (coreMap e ⟨q, hq⟩) v)
  change QuotientGroup.mk' (E e) q * (v : M e ⧸ E e) =
    (v : M e ⧸ E e) * QuotientGroup.mk' (E e) q at hc
  rw [hc, mul_inv_cancel_right]

/-- The actual action of M/Q on Q's image in M/Φ(Q). -/
noncomputable def frattiniConjugation
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    (M e ⧸ Q e) →* MulAut (Qbar e) :=
  QuotientGroup.lift (Q e)
    ((MulAut.conjNormal (H := Qbar e)).comp (QuotientGroup.mk' (E e)))
    (Q_le_frattini_conjugation_ker e)

theorem frattiniConjugation_apply
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (m : M e) (v : Qbar e) :
    (frattiniConjugation e (QuotientGroup.mk' (Q e) m) v : M e ⧸ E e) =
      QuotientGroup.mk' (E e) m * (v : M e ⧸ E e) *
        (QuotientGroup.mk' (E e) m)⁻¹ := rfl

/-- The binary module on the literal embedded Frattini quotient. -/
noncomputable def frattiniRepresentation
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    Representation (ZMod 2) (M e ⧸ Q e) (Additive (Qbar e)) where
  toFun h := (frattiniConjugation e h).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul ((frattiniConjugation e 1) v.toMul) = v
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul ((frattiniConjugation e (a * b)) v.toMul) = _
    rw [map_mul]
    rfl

theorem frattiniRepresentation_apply
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (m : M e) (v : Additive (Qbar e)) :
    ((frattiniRepresentation e (QuotientGroup.mk' (Q e) m) v).toMul : M e ⧸ E e) =
      QuotientGroup.mk' (E e) m * (v.toMul : M e ⧸ E e) *
        (QuotientGroup.mk' (E e) m)⁻¹ := rfl

/-- Compatibility with the literal core projection, hence with Q/Φ(Q). -/
theorem frattiniRepresentation_coreMap
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (m : M e) (q : Q e) :
    frattiniRepresentation e (QuotientGroup.mk' (Q e) m) (Additive.ofMul (coreMap e q)) =
      Additive.ofMul (coreMap e (MulAut.conjNormal m q)) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [frattiniRepresentation_apply]
  change QuotientGroup.mk' (E e) m * QuotientGroup.mk' (E e) (q : M e) *
    (QuotientGroup.mk' (E e) m)⁻¹ = QuotientGroup.mk' (E e) (m * (q : M e) * m⁻¹)
  rw [map_mul, map_mul, map_inv]

/-- Fixed vectors are exactly the centralizer occurring in the fusion theorem. -/
theorem frattiniRepresentation_fixed_iff
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (m : M e) (v : Additive (Qbar e)) :
    frattiniRepresentation e (QuotientGroup.mk' (Q e) m) v = v ↔
      (v.toMul : M e ⧸ E e) ∈ centralizer ({QuotientGroup.mk' (E e) m} : Set _) := by
  rw [← Additive.toMul.injective.eq_iff, ← Subtype.val_inj,
    frattiniRepresentation_apply, mul_inv_eq_iff_eq_mul,
    mem_centralizer_singleton_iff]
  exact eq_comm

/-- The linear fixed-displacement conclusion gives the literal group-theoretic
premise needed by coset_fusion_mod_frattini. -/
theorem fixed_le_commutator_of_frattini_displacement
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) (j : M e)
    (hfixed : ∀ v : Additive (Qbar e),
      frattiniRepresentation e (QuotientGroup.mk' (Q e) j) v = v →
      ∃ w : Additive (Qbar e),
        frattiniRepresentation e (QuotientGroup.mk' (Q e) j) w - w = v) :
    Qbar e ⊓ centralizer ({QuotientGroup.mk' (E e) j} : Set _) ≤
      ⁅Qbar e, zpowers (QuotientGroup.mk' (E e) j)⁆ := by
  rintro v ⟨hv, hc⟩
  obtain ⟨w, hw⟩ := hfixed (Additive.ofMul ⟨v, hv⟩)
    ((frattiniRepresentation_fixed_iff e j _).mpr hc)
  have he := congrArg (fun a : Additive (Qbar e) => (a.toMul : M e ⧸ E e)) hw
  simp only [toMul_sub, div_eq_mul_inv, coe_mul, coe_inv, toMul_ofMul] at he
  rw [frattiniRepresentation_apply] at he
  rw [← he, commutator_comm]
  exact commutator_mem_commutator (mem_zpowers _) w.toMul.property

/-- The actual fusion consumer, with its hypothesis expressed on the binary action. -/
theorem coset_fusion_of_frattini_displacement
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) (j : M e)
    (hj : orderOf (QuotientGroup.mk' (E e) j) = 2)
    (hfixed : ∀ v : Additive (Qbar e),
      frattiniRepresentation e (QuotientGroup.mk' (Q e) j) v = v →
      ∃ w : Additive (Qbar e),
        frattiniRepresentation e (QuotientGroup.mk' (Q e) j) w - w = v)
    (x : M e) (hx : x ^ 2 = 1)
    (hcoset : QuotientGroup.mk' (Q e) x = QuotientGroup.mk' (Q e) j) :
    ∃ q : Q e, QuotientGroup.mk' (E e) ((q : M e) * j * (q : M e)⁻¹) =
      QuotientGroup.mk' (E e) x :=
  coset_fusion_mod_frattini e j hj
    (fixed_le_commutator_of_frattini_displacement e j hfixed) x hx hcoset

/-- The covering normalizer also has a self-centralizing two-core. -/
theorem Q_selfCentralizing
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) :
    centralizer (Q e : Set (M e)) ≤ Q e := by
  intro m hm
  rw [Q_eq_model_core_preimage e hZ]
  apply Sporadic.LeechRelated.HS.BlockNormalizer.baseNormalizer_selfCentralizing
  intro q hq
  have hqmap : q ∈ (Q e).map (localMap e) := by
    rwa [Q_map_localMap e hZ]
  obtain ⟨a, ha, rfl⟩ := hqmap
  simpa only [map_mul] using congrArg (localMap e) (hm a ha)

/-- Faithfulness follows from the exact Burnside--Frattini action kernel.
It requires neither an abelian-core assumption nor a dimension calculation. -/
theorem frattiniRepresentation_injective
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) :
    Function.Injective (frattiniRepresentation e) := by
  apply (frattiniRepresentation e).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro a ha
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Q e) a
  change QuotientGroup.mk' (Q e) m = 1
  apply (QuotientGroup.eq_one_iff m).mpr
  change m ∈ pCore 2 (M e)
  rw [← pCore_frattini_action_kernel 2 (Q_selfCentralizing e hZ)]
  apply MulEquiv.ext
  intro v
  change quotientAut (frattini (Q e)) (MulAut.conjNormal m) v = v
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (frattini (Q e)) v
  apply (frattiniEquiv e).injective
  rw [quotientAut_apply_mk, frattiniEquiv_mk, frattiniEquiv_mk]
  apply Subtype.ext
  have hf := congrArg (fun f : Module.End (ZMod 2) (Additive (Qbar e)) =>
    ((f (Additive.ofMul (coreMap e q))).toMul : M e ⧸ E e)) ha
  change ((frattiniRepresentation e (QuotientGroup.mk' (Q e) m)
    (Additive.ofMul (coreMap e q))).toMul : M e ⧸ E e) =
      QuotientGroup.mk' (E e) (q : M e) at hf
  rw [frattiniRepresentation_apply] at hf
  change QuotientGroup.mk' (E e) (m * (q : M e) * m⁻¹) = _
  simpa only [map_mul, map_inv, toMul_ofMul, coreMap_val] using hf

/-- Order eight of the embedded Frattini subgroup gives a four-dimensional module. -/
theorem frattiniRepresentation_finrank
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (hE : Nat.card (E e) = 8) :
    Module.finrank (ZMod 2) (Additive (Qbar e)) = 4 := by
  have hphi : Nat.card (frattini (Q e)) = 8 := by
    rw [← card_subtype (Q e) (frattini (Q e))]
    exact hE
  have hcount := card_eq_card_quotient_mul_card_subgroup (frattini (Q e))
  rw [Q_card_eq_128 e hZ, hphi,
    Nat.card_congr (frattiniEquiv e).toEquiv] at hcount
  have hc : Nat.card (Qbar e) = 16 := by omega
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (Qbar e))
  change Nat.card (Qbar e) = _ at hpow
  rw [hc, Nat.card_zmod] at hpow
  exact Nat.pow_right_injective (by decide : 1 < 2) hpow.symm

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
