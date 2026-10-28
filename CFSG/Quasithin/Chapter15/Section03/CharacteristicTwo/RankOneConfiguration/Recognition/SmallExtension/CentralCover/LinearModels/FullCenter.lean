module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.LinearThree

/-!
# From the classified whole center to the literal coefficient quotient

The C.1.34 input identifies the whole center (or, in the abelian cases, the
whole commutator core) equivariantly. Exponent two and O₂(L)-centralization
are derived from these coordinates. With no fixed vectors, the literal
central kernel is trivial, giving a CenterModel on Z(Q)/C_Z(Q)(L).
Conjugating the actor and all coefficient copies together preserves every
compatibility. These are consequences of explicit classified module inputs;
this module does not assert the unfinished MS classification.

Source: Aschbacher--Smith, C.1.34(1)--(3), printed p.136, and the proof of
15.3.31, printed p.1132.
-/

@[expose] public section

open Subgroup Representation
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
open CentralCover
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.LinearModels
variable {G A V : Type*} [Group G] [Group A] [AddCommGroup V] [Module (ZMod 2) V]

/-- Actual whole-center coordinates for the specified quotient actor. -/
structure FullCenter (L : Subgroup G) (ρ : Representation (ZMod 2) A V) where
  quotientIso : (L ⧸ pCore 2 L) ≃* A
  equiv : coreCenter L ≃* Multiplicative V
  action : ∀ (l : L) (z : coreCenter L),
    equiv (centerConjugate L l z) = Multiplicative.ofAdd
      (ρ (quotientIso (QuotientGroup.mk' (pCore 2 L) l)) (equiv z).toAdd)

namespace FullCenter
variable {L : Subgroup G} {ρ : Representation (ZMod 2) A V} (c : FullCenter L ρ)

def actor : L →* A := c.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

theorem actor_surjective : Function.Surjective c.actor :=
  c.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)

include c in
theorem core_centralizes : L.pCoreIn 2 ≤ centralizer (coreCenter L : Set G) := by
  rintro x ⟨l, hl, rfl⟩
  apply mem_centralizer_iff.mpr
  intro z hz
  have he := c.action l ⟨z,hz⟩
  have hq : QuotientGroup.mk' (pCore 2 L) l = 1 := (QuotientGroup.eq_one_iff _).mpr hl
  rw [hq, map_one, map_one] at he
  have hconj : centerConjugate L l ⟨z,hz⟩ = ⟨z,hz⟩ := c.equiv.injective he
  have hh := congrArg Subtype.val hconj
  change (l : G) * z * (l : G)⁻¹ = z at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

include c in
theorem elementary : IsElementaryAbelian 2 (coreCenter L) := by
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · exact le_centralizer_iff_isMulCommutative.mp
      (inf_le_right.trans (centralizer_le (show coreCenter L ≤ extensionCore L from inf_le_left)))
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro z
    apply c.equiv.injective
    rw [map_pow, map_one]
    change Multiplicative.ofAdd (2 • (c.equiv z).toAdd) = Multiplicative.ofAdd 0
    apply congrArg Multiplicative.ofAdd
    calc
      (2 : ℕ) • (c.equiv z).toAdd = (2 : ZMod 2) • (c.equiv z).toAdd :=
        (Nat.cast_smul_eq_nsmul (R := ZMod 2) 2 (c.equiv z).toAdd).symm
      _ = 0 := by rw [show (2 : ZMod 2) = 0 by decide, zero_smul]

include c in
theorem kernel_eq_bot (hfixed : ∀ v : V, (∀ a : A, ρ a v = v) → v = 0) :
    centerKernel L = ⊥ := by
  apply _root_.eq_bot_iff.mpr
  intro z hz
  change z = 1
  apply c.equiv.injective
  rw [map_one]
  apply congrArg Multiplicative.ofAdd
  apply hfixed
  intro a
  obtain ⟨l,rfl⟩ := c.actor_surjective a
  have hh : centerConjugate L l z = z := by
    apply Subtype.ext
    change (l : G) * (z : G) * (l : G)⁻¹ = z
    have hc : (l : G) * (z : G) = (z : G) * (l : G) :=
      mem_centralizer_iff.mp hz l l.property
    rw [hc, mul_inv_cancel_right]
  exact (congrArg Multiplicative.toAdd (c.action l z)).symm.trans (by rw [hh]; rfl)

noncomputable def model (hfixed : ∀ v : V, (∀ a : A, ρ a v = v) → v = 0) :
    CenterModel L ρ where
  quotientIso := c.quotientIso
  moduleIso := (QuotientGroup.quotientMulEquivOfEq (c.kernel_eq_bot hfixed)).trans
    (QuotientGroup.quotientBot.trans c.equiv)
  intertwining l z := c.action l z
  core_centralizes := c.core_centralizes

/-- Change all copies simultaneously by the same actor. -/
def actionEquiv (a : A) : Multiplicative V ≃* Multiplicative V where
  toFun v := Multiplicative.ofAdd (ρ a v.toAdd)
  invFun v := Multiplicative.ofAdd (ρ a⁻¹ v.toAdd)
  left_inv v := congrArg Multiplicative.ofAdd (ρ.inv_self_apply a v.toAdd)
  right_inv v := congrArg Multiplicative.ofAdd (ρ.self_inv_apply a v.toAdd)
  map_mul' v w := congrArg Multiplicative.ofAdd ((ρ a).map_add v.toAdd w.toAdd)

def recoordinate (a : A) : FullCenter L ρ where
  quotientIso := c.quotientIso.trans (MulAut.conj a)
  equiv := c.equiv.trans (actionEquiv (ρ := ρ) a)
  action l z := by
    change Multiplicative.ofAdd (ρ a (c.equiv (centerConjugate L l z)).toAdd) = _
    rw [c.action]
    apply congrArg Multiplicative.ofAdd
    change ρ a (ρ (c.actor l) (c.equiv z).toAdd) =
      ρ (a * c.actor l * a⁻¹) (ρ a (c.equiv z).toAdd)
    rw [map_mul, map_mul]
    simp only [Module.End.mul_apply, inv_self_apply]

theorem recoordinate_actor (a : A) :
    (c.recoordinate a).actor = (MulAut.conj a).toMonoidHom.comp c.actor := rfl

end FullCenter
/-- The classified abelian core, before identifying it with its center. -/
structure AbelianCore (L : Subgroup G) (ρ : Representation (ZMod 2) A V) where
  quotientIso : (L ⧸ pCore 2 L) ≃* A
  equiv : extensionCore L ≃* Multiplicative V
  action : ∀ (l : L) (x y : extensionCore L),
    (y : G) = (l : G) * (x : G) * (l : G)⁻¹ →
    equiv y = Multiplicative.ofAdd
      (ρ (quotientIso (QuotientGroup.mk' (pCore 2 L) l)) (equiv x).toAdd)

namespace AbelianCore
variable {L : Subgroup G} {ρ : Representation (ZMod 2) A V} (c : AbelianCore L ρ)
include c in
theorem center_eq : coreCenter L = extensionCore L := by
  apply le_antisymm inf_le_left
  intro z hz
  refine ⟨hz, mem_centralizer_iff.mpr ?_⟩
  intro x hx
  have hh : (⟨x,hx⟩ : extensionCore L) * ⟨z,hz⟩ = ⟨z,hz⟩ * ⟨x,hx⟩ := by
    apply c.equiv.injective
    rw [map_mul, map_mul, mul_comm]
  exact congrArg Subtype.val hh

def fullCenter : FullCenter L ρ where
  quotientIso := c.quotientIso
  equiv := (MulEquiv.subgroupCongr c.center_eq).trans c.equiv
  action l _z := c.action l _ _ rfl

end AbelianCore

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover.LinearModels
