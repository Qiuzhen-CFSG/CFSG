module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreRecognition.SylowInputs.TwoPart.CoreFixed

/-!
# The local cubic normalizer has order 48

Write H = C_G(z) and Q = O₂(H). The checked cubic normal form gives
|C_Q(X)| = 8. Coprime normalizing subgroups commute, so N_Q(X) = C_Q(X).
The image of N_H(X) in H/Q lies in the normalizer of a cubic subgroup
of the actual A₅ quotient, of order six. Thus |N_H(X)| = 8r with r ≤ 6.
The normalizer congruence modulo nine and |H| = 1920 force r = 6.

This argument uses only the original seed and its literal quotient map.
It supplies the order required by the SL₂(3) pair construction in 47.5;
no assertion about a semidihedral Sylow subgroup is used.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.3 and 47.5,
printed pp.262–263.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
variable {G : Type*} [Group G] [Finite G]

/-- The original involution centralizer's cubic normalizer, with no later
three-local recognition or numerical premise. -/
theorem local_normalizer_card (D : Seed G) : Nat.card (SL23Local.localNormalizer D) = 48 := by
  let H := involutionCentralizer D.z
  let Q := localCore D.z
  let Y := D.X.subgroupOf H
  let N := normalizer (Y : Set H)
  let q := QuotientGroup.mk' Q
  let f := q.comp N.subtype
  have hY : Nat.card Y = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe D.X_le).toEquiv).trans D.card_X
  have hd : Disjoint Q Y := disjoint_of_coprime_natCard (by
    rw [D.localType.core_card, hY]
    decide)
  have hi : Function.Injective (q.comp Y.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro y hy
    apply Subtype.ext
    exact (disjoint_def.mp hd) ((QuotientGroup.eq_one_iff y.val).mp hy) y.property
  have hYq : Nat.card (Y.map q) = 3 := by
    calc
      _ = Nat.card (q.comp Y.subtype).range := by rw [MonoidHom.range_comp, range_subtype]
      _ = Nat.card Y := Nat.card_congr (MonoidHom.ofInjective hi).symm.toEquiv
      _ = 3 := hY
  have hXQ : D.X ≤ normalizer (ambientCore D.z : Set G) := by
    rw [D.localType.normalizer_core]
    exact D.X_le
  have hdG : Disjoint (ambientCore D.z) D.X := disjoint_of_coprime_natCard (by
    rw [D.localType.ambientCore_card, D.card_X]
    decide)
  have hRN : ambientCore D.z ⊓ normalizer (D.X : Set G) = ambientCore D.z ⊓ C D := by
    apply le_antisymm
    · apply le_inf inf_le_left
      apply commutator_eq_bot_iff_le_centralizer.mp
      apply le_bot_iff.mp
      rw [← hdG.eq_bot]
      refine le_inf ?_ (le_normalizer_iff_commutator_le_right.mp inf_le_right)
      exact (commutator_mono inf_le_left le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hXQ)
    · exact inf_le_inf_left _ (C_le_M D)
  have hk : f.ker = Q.subgroupOf N := by
    ext n
    exact QuotientGroup.eq_one_iff n.val
  have hkm : f.ker.map (H.subtype.comp N.subtype) = ambientCore D.z ⊓ C D := by
    rw [← map_map, hk, subgroupOf_map_subtype, Subgroup.map_inf _ _ _ H.subtype_injective]
    change ambientCore D.z ⊓ (normalizer (Y : Set H)).map H.subtype = _
    rw [← SL23Local.localNormalizer_eq_map D]
    change ambientCore D.z ⊓ (H ⊓ normalizer (D.X : Set G)) = _
    rw [← inf_assoc, inf_eq_left.mpr (ambientCore_le D.z), hRN]
  have hkcard : Nat.card f.ker = 8 := by
    rw [← card_map_of_injective (f := H.subtype.comp N.subtype)
        (H.subtype_injective.comp N.subtype_injective),
      hkm, CoreSylowInputs.core_centralizer_card D]
  have himage : Nat.card f.range ≤ 6 := by
    have h := card_le_of_le (Y.le_normalizer_map q)
    rw [alternatingGroup.FiveLocalGeometry.cubic_normalizer_card
      D.localType.quotient_equiv.some (Y.map q) hYq] at h
    simpa only [f, MonoidHom.range_comp, range_subtype] using h
  have hprod := f.ker.index_mul_card
  rw [index_ker, hkcard] at hprod
  have hmod := Sylow.card_normalizer_modEq_card (p := 3) (n := 1) (H := Y) (by simpa using hY)
  rw [D.localType.centralizer_card] at hmod
  have hNc : Nat.card N = 48 := by
    change Nat.card N % 9 = 1920 % 9 at hmod
    omega
  rw [SL23Local.localNormalizer_eq_map, card_map_of_injective H.subtype_injective]
  exact hNc

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
