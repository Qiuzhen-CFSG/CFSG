module

public import Stellmacher.Recognition.Parrott.SylowBWQuadraticInputs
public import Stellmacher.Recognition.Parrott.DerivedCentralizer
public import Theory.GroupAction.QuotientCommutatorPairing
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The invariant central commutator pairing of Parrott's core

Put H = C_G(z), J = O₂(H), D = J′ and Z = Z(J). The literal quotients
V = J/D and W = D/Z carry a pairing into the multiplicative group of
ZMod 2. Its representative value is the actual central commutator [w,b],
transported through an equivalence from Z(J). This orientation is the
inverse of [b,w]; the two agree because the center has order two.

The checked structure theorem gives D = Z₂(J), D abelian, and |Z(J)| = 2.
The quotient commutator pairing therefore descends in both variables.
Transferring the ambient derived self-centralizer theorem gives C_J(D) = D,
which proves injectivity of V into the binary dual of W. Conjugation
preserves the commutation test, and a binary value is determined by whether
it is one. Hence the pairing is invariant under every pair of actions with
the literal conjugation evaluation formulas.

Source: David Parrott, *A characterization of the Tits' simple group*
(1972), pp.673–674.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] [Finite G] {z : G}
set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
local notation "J" => pCore 2 H
local notation "D" => commutator J
set_option quotPrecheck false in
local notation "Z" => (center J).subgroupOf D
local notation "V" => J ⧸ D
local notation "W" => D ⧸ Z

/-- Commutators between the derived core and the core lie in its center. -/
public theorem parrott_core_commutator_mem_center (h : ParrottCentralizerHypotheses z)
    (b : J) (w : D) : ⁅(w : J), b⁆ ∈ center J := by
  have hUpper := (parrott_centralizer_structure z h).2.2.2.2.1
  have hcomm : ⁅D, ⊤⁆ ≤ center J := by
    rw [hUpper]
    exact (commutator_upperCentralSeries_top_le J 1).trans_eq (Subgroup.upperCentralSeries_one J)
  exact hcomm (commutator_mem_commutator w.property (mem_top b))

/-- The derived subgroup is self-centralizing inside the actual core. -/
public theorem parrott_core_derived_centralizer (h : ParrottCentralizerHypotheses z) :
    centralizer (D : Set J) = D := by
  let i := (H).subtype.comp (J).subtype
  have hi : Function.Injective i := (H).subtype_injective.comp (J).subtype_injective
  apply le_antisymm
  · intro b hb
    have him : i b ∈ centralizer ((D).map i : Set G) := by
      rintro _ ⟨d, hd, rfl⟩
      exact congrArg i (hb d hd)
    rw [parrott_derived_centralizer z h] at him
    obtain ⟨d, hd, heq⟩ := him
    exact hi heq ▸ hd
  · have hElem := (parrott_centralizer_structure z h).2.2.2.2.2.1
    let : IsElementaryAbelian 2 D := hElem
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance

/-- The actual central commutator descends to a nondegenerate binary pairing,
with its representative evaluation and exact commutation test. -/
public theorem parrott_core_pairing (h : ParrottCentralizerHypotheses z) :
    ∃ (eZ : center J ≃* Multiplicative (ZMod 2))
      (p : V →* (W →* Multiplicative (ZMod 2))),
      Function.Injective p ∧
      (∀ (b : J) (w : D),
        p (QuotientGroup.mk' D b) (QuotientGroup.mk' Z w) = 1 ↔ Commute b (w : J)) ∧
      (∀ (b : J) (w : D),
        p (QuotientGroup.mk' D b) (QuotientGroup.mk' Z w) =
          eZ ⟨⁅(w : J), b⁆, parrott_core_commutator_mem_center h b w⟩) := by
  classical
  obtain ⟨hZmap, _, _, _, hUpper, hElem, _, _⟩ := parrott_centralizer_structure z h
  let : IsElementaryAbelian 2 D := hElem
  have hZD : center J ≤ D := by
    rw [hUpper]
    simpa only [Subgroup.upperCentralSeries_one] using
      Subgroup.upperCentralSeries_mono J (show 1 ≤ 2 by decide)
  have hZcard : Nat.card (center J) = 2 := by
    have hc := card_map_of_injective (K := center J)
      (f := (H).subtype.comp (J).subtype)
      ((H).subtype_injective.comp (J).subtype_injective)
    rw [hZmap, Nat.card_zpowers, h.involution] at hc
    exact hc.symm
  let eZ : center J ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hZcard (by simp)
  have hbot : (⊥ : Subgroup J).subgroupOf (center J) = (⊥ : Subgroup (center J)) := by
    ext c; simp
  let : ((⊥ : Subgroup J).subgroupOf (center J)).Normal := hbot.symm ▸ inferInstance
  let e0 : (center J ⧸ (⊥ : Subgroup J).subgroupOf (center J)) ≃* center J :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have hcomm : ⁅D, ⊤⁆ ≤ center J := by
    rw [hUpper]
    exact (commutator_upperCentralSeries_top_le J 1).trans_eq (Subgroup.upperCentralSeries_one J)
  have hZcomm : ⁅center J, (⊤ : Subgroup J)⁆ ≤ ⊥ := by
    rw [le_bot_iff, commutator_comm, commutator_eq_bot_iff_le_centralizer]
    intro b _ c hc
    exact (mem_center_iff.mp hc b).symm
  let raw := (quotientCommutatorPairing D ⊤ (center J) ⊥ hZD hcomm hZcomm).compr₂
    (e0.trans eZ).toMonoidHom
  have hraw_eval (w : D) (b : (⊤ : Subgroup J)) :
      raw w b = eZ ⟨⁅(w : J), (b : J)⁆,
        parrott_core_commutator_mem_center h b w⟩ := by
    dsimp only [raw]
    rw [MonoidHom.compr₂_apply, quotientCommutatorPairing_apply]
    rfl
  have hraw_one (w : D) (b : (⊤ : Subgroup J)) :
      raw w b = 1 ↔ Commute (w : J) (b : J) := by
    rw [hraw_eval, ← eZ.map_one, eZ.injective.eq_iff, Subtype.ext_iff]
    exact commutatorElement_eq_one_iff_mul_comm
  have hkillZ : Z ≤ raw.ker := by
    intro c hc
    ext b
    apply (hraw_one c b).mpr
    exact (mem_center_iff.mp hc b).symm
  let first : W →* ((⊤ : Subgroup J) →* Multiplicative (ZMod 2)) :=
    QuotientGroup.lift Z raw hkillZ
  let topLift : J →* (⊤ : Subgroup J) := (Subgroup.topEquiv : (⊤ : Subgroup J) ≃* J).symm
  have hkillD (w : W) : D ≤ ((first w).comp topLift).ker := by
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective Z w
    intro b hb
    change raw w (topLift b) = 1
    apply (hraw_one w (topLift b)).mpr
    exact congrArg (fun t : D => (t : J)) (mul_comm w (⟨b, hb⟩ : D))
  let pairing : W →* (V →* Multiplicative (ZMod 2)) := {
    toFun w := QuotientGroup.lift D ((first w).comp topLift) (hkillD w)
    map_one' := by
      apply MonoidHom.ext
      intro v
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective D v
      change first 1 (topLift b) = 1
      simp
    map_mul' w w' := by
      apply MonoidHom.ext
      intro v
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective D v
      change first (w * w') (topLift b) = first w (topLift b) * first w' (topLift b)
      rw [map_mul]
      rfl }
  let p := pairing.flip
  have heval (b : J) (w : D) :
      p (QuotientGroup.mk' D b) (QuotientGroup.mk' Z w) =
        eZ ⟨⁅(w : J), b⁆, parrott_core_commutator_mem_center h b w⟩ :=
    hraw_eval w (topLift b)
  have htest (b : J) (w : D) :
      p (QuotientGroup.mk' D b) (QuotientGroup.mk' Z w) = 1 ↔ Commute b (w : J) := by
    exact (hraw_one w (topLift b)).trans ⟨Commute.symm, Commute.symm⟩
  refine ⟨eZ, p, ?_, htest, heval⟩
  · apply (MonoidHom.ker_eq_bot_iff p).mp
    apply bot_unique
    intro v hv
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective D v
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [← parrott_core_derived_centralizer h]
    intro w hw
    have hh := congrArg (fun f : W →* Multiplicative (ZMod 2) =>
      f (QuotientGroup.mk' Z ⟨w, hw⟩)) hv
    exact ((htest b ⟨w, hw⟩).mp hh).symm.eq

omit [Finite G] in
/-- Every binary pairing with the literal commutation test is invariant under
actions evaluating as conjugation by the involution centralizer. -/
public theorem parrott_core_pairing_invariant
    (p : V →* (W →* Multiplicative (ZMod 2)))
    (htest : ∀ (b : J) (w : D),
      p (QuotientGroup.mk' D b) (QuotientGroup.mk' Z w) = 1 ↔ Commute b (w : J))
    (L : (H ⧸ J) →* MulAut V) (R : (H ⧸ J) →* MulAut W)
    (hL : ∀ (a : H) (d d' : J), (d' : H) = a * (d : H) * a⁻¹ →
      L (QuotientGroup.mk' J a) (QuotientGroup.mk' D d) = QuotientGroup.mk' D d')
    (hR : ∀ (a : H) (d d' : D), ((d' : J) : H) = a * ((d : J) : H) * a⁻¹ →
      R (QuotientGroup.mk' J a) (QuotientGroup.mk' Z d) = QuotientGroup.mk' Z d') :
    ∀ a v w, p (L a v) (R a w) = p v w := by
  intro a v w
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective J a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective D v
  obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective Z w
  let α : MulAut J := MulAut.conjNormal a
  let b' := α b
  let d' := MulAut.characteristic D α d
  have hb' : (b' : H) = a * (b : H) * a⁻¹ := rfl
  have hd' : ((d' : J) : H) = a * ((d : J) : H) * a⁻¹ := rfl
  rw [hL a b b' hb', hR a d d' hd']
  have hbinary : ∀ x y : Multiplicative (ZMod 2), (x = 1 ↔ y = 1) → x = y := by decide
  apply hbinary
  rw [htest, htest]
  change Commute (α b) (α (d : J)) ↔ Commute b (d : J)
  exact ⟨Commute.of_map α.injective, fun hc => hc.map α⟩

/-- The invariant nondegenerate central commutator pairing, for any supplied
pair of quotient actions with the literal conjugation evaluations. -/
public theorem parrott_core_invariant_pairing (h : ParrottCentralizerHypotheses z)
    (L : (H ⧸ J) →* MulAut V) (R : (H ⧸ J) →* MulAut W)
    (hL : ∀ (a : H) (d d' : J), (d' : H) = a * (d : H) * a⁻¹ →
      L (QuotientGroup.mk' J a) (QuotientGroup.mk' D d) = QuotientGroup.mk' D d')
    (hR : ∀ (a : H) (d d' : D), ((d' : J) : H) = a * ((d : J) : H) * a⁻¹ →
      R (QuotientGroup.mk' J a) (QuotientGroup.mk' Z d) = QuotientGroup.mk' Z d') :
    ∃ (eZ : center J ≃* Multiplicative (ZMod 2))
      (p : V →* (W →* Multiplicative (ZMod 2))),
      Function.Injective p ∧
      (∀ (b : J) (w : D),
        p (QuotientGroup.mk' D b) (QuotientGroup.mk' Z w) = 1 ↔ Commute b (w : J)) ∧
      (∀ (b : J) (w : D),
        p (QuotientGroup.mk' D b) (QuotientGroup.mk' Z w) =
          eZ ⟨⁅(w : J), b⁆, parrott_core_commutator_mem_center h b w⟩) ∧
      ∀ a v w, p (L a v) (R a w) = p v w := by
  obtain ⟨eZ, p, hinj, htest, heval⟩ := parrott_core_pairing h
  exact ⟨eZ, p, hinj, htest, heval, parrott_core_pairing_invariant p htest L R hL hR⟩
end Stellmacher.Recognition
