module

public import CFSG.Quasithin.ChapterC.Defs
public import Theory.GroupTheory.PCorePrimeToIndex

/-!+# Elementary ingredients of the MS-pair hypotheses

These are precisely (MS2)(a) and (MS3) of Aschbacher–Smith C.1.31,
combined manuscript (1 March 2004), printed p.135. They are separate
ingredients, not a definition of an MS-pair: the SQTK and rank-two component
conditions of (MS1), and the exceptional G₂(2) parabolic alternative (MS2)(b),
are still required for that definition.

The odd-index condition puts O₂(G) inside R by Sylow theory. The characteristic
condition is the second conjunct of (PU), with no radicality assumption.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC

variable {G : Type*} [Group G]

/-- Alternative (MS2)(a), with the core mapped from H to the ambient group. -/
def MSOddIndexRadical (R : Subgroup G) : Prop :=
  ∃ H : Subgroup G, H < ⊤ ∧ Odd H.index ∧ (pCore 2 H).map H.subtype = R

/-- Exactly (MS3): no nontrivial characteristic subgroup of R is normal in G. -/
def MSCharacteristicCondition (R : Subgroup G) : Prop :=
  ∀ C : Subgroup R, C.Characteristic → C ≠ ⊥ → ¬ (C.map R.subtype).Normal

/-- In alternative (MS2)(a), R is a two-subgroup. -/
theorem MSOddIndexRadical.isPGroup {R : Subgroup G} (hR : MSOddIndexRadical R) :
    IsPGroup 2 R := by
  obtain ⟨H, _, _, rfl⟩ := hR
  exact pCore_isPGroup.map H.subtype

/-- The consequence of (MS2)(a) used in applying MS93. -/
theorem MSOddIndexRadical.twoCore_le [Finite G] {R : Subgroup G}
    (hR : MSOddIndexRadical R) : pCore 2 G ≤ R := by
  obtain ⟨H, _, hodd, rfl⟩ := hR
  exact pCore_le_map_pCore_of_prime_not_dvd_index H hodd.not_two_dvd_nat

/-- The characteristic condition together with radicality is precisely (PU). -/
theorem pushingUp_iff_radical_and_msCharacteristic (R : Subgroup G) :
    PushingUp R ↔ IsTwoRadical R ∧ MSCharacteristicCondition R := Iff.rfl

/-- Every characteristic subgroup normal in G is trivial under (MS3). -/
theorem MSCharacteristicCondition.eq_bot_of_normal {R : Subgroup G}
    (hR : MSCharacteristicCondition R) (C : Subgroup R) [hC : C.Characteristic]
    (hn : (C.map R.subtype).Normal) : C = ⊥ := by
  by_contra hne
  exact hR C hC hne hn

end CFSG.Quasithin.ChapterC
