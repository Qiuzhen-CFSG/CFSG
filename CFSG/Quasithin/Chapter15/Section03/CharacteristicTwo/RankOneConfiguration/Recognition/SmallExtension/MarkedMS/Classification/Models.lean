module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.RankTwoQuotient
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.Geometry
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Comparing the small marked groups with the MS quotient models

The actual marked star group has order 168, 360, or 6048. An Sp₄(4)
block would give a centerless core quotient of order 979200. For SL₃(F),
the compatible central-core quotient is PSL₃(F), whose upper unipotent
subgroup has order |F|³. None of the small orders is divisible by 64,
so a field of order 2ⁿ must have n = 1. Coefficient transport then gives
an actual SL₃(2) equivalence, not just an order identification.

The surviving block predicates retain their entire equivariant natural
module and relative block assertions. Their concrete centers are trivial;
quasisimplicity already supplied by the component therefore proves
simplicity of the core quotient, also for the derived binary G₂ carrier.
The exceptional triple-cover comparison is handled in `BlockKernel`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.30–32,
printed p.135, and the first paragraph of the proof of 15.3.31, p.1132.
The model facts reuse the attributed ATLAS ports; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G]

private def centerQuotientCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (centerCongr e ⟨x, hx⟩).property
    · intro x hx
      exact ⟨e.symm x, (centerCongr e).symm ⟨x, hx⟩ |>.property,
        e.apply_symm_apply x⟩)

private theorem center_eq_bot_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  exact e.map_eq_one_iff.mp (hz.le ((centerCongr e ⟨x, hx⟩).property))

private theorem simple_of_quasisimple_centerless {A : Type*} [Group A]
    [IsQuasisimple A] (hz : center A = ⊥) : IsSimpleGroup A := by
  let := IsQuasisimple.simple (G := A)
  exact (((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).symm).isSimpleGroup

/-- Orders of the three actual marked carriers. -/
theorem marked_star_card (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hm : Parabolics.SmallParabolicMarking d I c.L) :
    Nat.card (d.starImage I c.L) = 168 ∨ Nat.card (d.starImage I c.L) = 360 ∨
      Nat.card (d.starImage I c.L) = 6048 := by
  cases hm with
  | linearThree m =>
    exact Or.inl ((Nat.card_congr m.equiv.toEquiv).trans Matrix.PSL3Two.card_SL)
  | symplecticDerived m =>
    right; left
    rw [Nat.card_congr (m.equiv.trans
      (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
        (by simp))).toEquiv, nat_card_alternatingGroup]
    norm_num
  | g2Derived m =>
    right; right
    rw [Nat.card_congr m.equiv.toEquiv,
      Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
      Atlas.G2.BinaryException.card_H]

/-- The Sp₄(4) quotient cannot be one of the three marked small groups. -/
theorem not_sp4FourBlock (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hm : Parabolics.SmallParabolicMarking d I c.L) : ¬ IsSp4FourBlock c.L := by
  rintro ⟨_, F, _, _, hF, rho, ⟨model⟩, _⟩
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (f := 2) hF
  let e := model.quotientIso
  let := c.core_quotient_quasisimple
  let := simple_of_quasisimple_centerless (center_eq_bot_of_equiv e
    Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot)
  have he : Nat.card (d.starImage I c.L) = 979200 := by
    rw [← Nat.card_congr (coreQuotientEquivStar d c hnormal P hP).toEquiv,
      Nat.card_congr e.toEquiv, Theory.SpecificGroups.SymplecticFour.card_sp, hF]
    norm_num
  rcases marked_star_card d c hm with h | h | h <;> omega

/-- Compare the actual projective quotient, force the binary degree, and
transport the full special-linear quotient along a field equivalence. -/
theorem linearThree_binary (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hnormal : (c.L.subgroupOf I).Normal)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (n : ℕ) (hn : 1 ≤ n) (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) F) :
    n = 1 ∧ Nonempty ((c.L ⧸ pCore 2 c.L) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  let f := (centralCoreQuotientEquivStar d c hnormal P hP hm).symm.trans
    ((centralPreimageQuotientEquiv (pCore 2 c.L)).trans (centerQuotientCongr e))
  have hd : 2 ^ (n * 3) ∣ Nat.card (d.starImage I c.L) := by
    rw [Nat.card_congr f.toEquiv, pow_mul, ← hF,
      ← Matrix.PSL3.LinearThree.card_unipotent F]
    exact card_subgroup_dvd_card (Matrix.PSL3.LinearThree.unipotent F)
  have hn1 : n = 1 := by
    by_contra h
    have h64 : 64 ∣ Nat.card (d.starImage I c.L) :=
      (pow_dvd_pow 2 (show 6 ≤ n * 3 by omega)).trans hd
    rcases marked_star_card d c hm with hc | hc | hc <;> rw [hc] at h64 <;>
      norm_num at h64
  refine ⟨hn1, ?_⟩
  let := Fintype.ofFinite F
  let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [hn1, pow_one, Nat.card_eq_fintype_card] using hF)).symm
  exact ⟨e.trans (Atlas.fieldEquivSL 3 ef)⟩

/-- The surviving C.1.32 alternatives, before C.1.34 specializes the
linear case. Both block cases retain their full natural-module predicates. -/
def CoreAlternatives (L S : Subgroup G) : Prop :=
  (IsBlock (L.subgroupOf (L ⊔ S)) ∧ IsAlternatingBlock L 6) ∨
  (IsBlock (L.subgroupOf (L ⊔ S)) ∧ IsG2TwoBlock L) ∨
  Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))

/-- Inherited quasisimplicity and the actual model centers give simplicity
for every surviving core quotient. -/
theorem coreAlternatives_simple {L S : Subgroup G}
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (h : CoreAlternatives L S) :
    IsSimpleGroup (L ⧸ pCore 2 L) := by
  let := hq
  apply simple_of_quasisimple_centerless
  change (_ ∧ _) ∨ (_ ∧ _) ∨ _ at h
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ | ⟨e⟩
  · obtain ⟨e⟩ := h.2.2.quotient_iso
    exact center_eq_bot_of_equiv e (alternatingGroup.center_eq_bot (by simp))
  · obtain ⟨e⟩ := h.quotient_model
    exact center_eq_bot_of_equiv e Theory.SpecificGroups.g2_derived_two_center_eq_bot
  · obtain ⟨e⟩ := e
    exact center_eq_bot_of_equiv e Matrix.PSL3Two.center_eq_bot

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

end
