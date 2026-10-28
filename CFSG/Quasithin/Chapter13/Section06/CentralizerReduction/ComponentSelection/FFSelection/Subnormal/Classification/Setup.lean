module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Action
public import Theory.Representation.BinaryOffender.CubicMovedRank

/-!
# The literal cubic input for the B.5.6 deductions

The hypothesis retains the ambient faithful action, its actual offender
subgroup, a subnormal cubic A, and a Sylow two-subgroup normalizing A.
The subgroup C lies in both the Sylow subgroup and the offender subgroup,
and A=[A,C]. No normality, factor placement or dimension bound is assumed.

Restriction to the normal offender subgroup preserves the cubic order,
subnormality, full commutator and the actual Sylow intersection. The
Chapter 13 application below constructs every field using the binary A₅
marking, the supplied Sylow of G_v, and the earlier local hypotheses.

Source: Aschbacher–Smith, B.5.3–6, printed pp.104–105, and the first
sentence of the proof of 13.6.10, printed p.928.
-/

@[expose] public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
universe u w
variable {D : Type u} [Group D] [Finite D]
    {W : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)

/-- The two outputs required by 13.6.10, on the original representation
and the normalizer in the original ambient group. This is an output
specification; its existence is not a hypothesis of `CubicHypothesis`. -/
def CubicBounds (A : Subgroup D) : Prop :=
  Module.finrank (ZMod 2) (moved ρ A) = 2 ∧ (normalizer (A : Set D)).index ≤ 2

/-- Genuine inputs for the conditional classification deduction. -/
structure CubicHypothesis (A : Subgroup D) (S : Sylow 2 D) (C : Subgroup D) : Prop where
  faithful : Function.Injective ρ
  twoCore : pCore 2 D = ⊥
  le_offender : A ≤ offenderSubgroup ρ
  subnormal : A.IsSubnormal
  card : Nat.card A = 3
  normalizes : (S : Subgroup D) ≤ normalizer (A : Set D)
  le_sylow : C ≤ (S : Subgroup D)
  actor_le_offender : C ≤ offenderSubgroup ρ
  full : A = ⁅A, C⁆

variable {ρ} {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}

omit [Finite D] in
/-- The cubic subgroup cannot lie in a trivial offender actor. -/
theorem CubicHypothesis.not_trivial (h : CubicHypothesis ρ A S C)
    (ht : Subsingleton (offenderSubgroup ρ)) : False := by
  let := ht
  have he : A = ⊥ := A.eq_bot_iff_forall.mpr (by
    intro a ha
    exact congrArg Subtype.val (Subsingleton.elim
      (⟨a, h.le_offender ha⟩ : offenderSubgroup ρ) 1))
  have hc := h.card
  rw [he] at hc
  simp at hc

omit [Finite D] in
/-- Intrinsic order is unchanged on restriction to the offender actor. -/
theorem CubicHypothesis.internal_card (h : CubicHypothesis ρ A S C) :
    Nat.card (A.subgroupOf (offenderSubgroup ρ)) = 3 :=
  (Nat.card_congr (subgroupOfEquivOfLe h.le_offender).toEquiv).trans h.card

/-- A subnormal cubic lies in the actual three-core of the offender actor. -/
theorem CubicHypothesis.internal_le_threeCore (h : CubicHypothesis ρ A S C) :
    A.subgroupOf (offenderSubgroup ρ) ≤ pCore 3 (offenderSubgroup ρ) := by
  let B := A.subgroupOf (offenderSubgroup ρ)
  have hp : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by simpa using h.internal_card)
  have ht : pCore 3 B = ⊤ := top_unique (le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩)
  have hh := pCoreIn_le_of_subnormal 3 (h.subnormal.subgroupOf (K := offenderSubgroup ρ))
  change (pCore 3 B).map B.subtype ≤ _ at hh
  simpa only [ht, ← MonoidHom.range_eq_map, range_subtype] using hh

omit [Finite D] in
/-- The full commutator uses the same C after restriction. -/
theorem CubicHypothesis.internal_full (h : CubicHypothesis ρ A S C) :
    A.subgroupOf (offenderSubgroup ρ) =
      ⁅A.subgroupOf (offenderSubgroup ρ), C.subgroupOf (offenderSubgroup ρ)⁆ := by
  apply map_injective (offenderSubgroup ρ).subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le h.le_offender,
    map_subgroupOf_eq_of_le h.actor_le_offender]
  exact h.full

/-- Intersecting the supplied Sylow with J gives an actual Sylow of J,
still normalizing the cubic and containing the same restricted C. -/
theorem CubicHypothesis.internal_sylow (h : CubicHypothesis ρ A S C) :
    ∃ R : Sylow 2 (offenderSubgroup ρ),
      (R : Subgroup (offenderSubgroup ρ)) = (S : Subgroup D).subgroupOf (offenderSubgroup ρ) ∧
      (R : Subgroup (offenderSubgroup ρ)) ≤
        normalizer (A.subgroupOf (offenderSubgroup ρ) : Set (offenderSubgroup ρ)) ∧
      C.subgroupOf (offenderSubgroup ρ) ≤ (R : Subgroup (offenderSubgroup ρ)) := by
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_normal (offenderSubgroup ρ)
  refine ⟨R, hR, ?_, ?_⟩
  · rw [hR, ← subgroupOf_normalizer_eq h.le_offender]
    exact fun _ hx => h.normalizes hx
  · rw [hR]
    exact fun _ hx => h.le_sylow hx

omit [Finite D] in
/-- Every branch already has the lower moved-space bound. -/
theorem CubicHypothesis.two_le_moved [FiniteDimensional (ZMod 2) W]
    (h : CubicHypothesis ρ A S C) : 2 ≤ Module.finrank (ZMod 2) (moved ρ A) :=
  two_le_finrank_subspaceCommutator_of_card_three ρ A h.faithful h.card

section Application
variable {G : Type u} [Group G] [Finite G]

/-- Literal Chapter 13 input. The order-three conclusion comes from the
marked A₅ seed and the earlier cubic two-core quotient, rather than being
assumed for the star image. -/
theorem marked_cubic_hypothesis {L V : Subgroup G} (s : A5Module.Marking L V)
    (T : Subgroup G)
    [IsElementaryAbelian 2 (internalUv (A5Module.markedZ s) (A5Module.markedV s))]
    (S : Sylow 2 (Gv (A5Module.markedV s)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s))).map
      (Gv (A5Module.markedV s)).subtype = Tv T (A5Module.markedV s))
    (hT : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hcore : pCore 2 (Gstar (A5Module.markedZ s) (A5Module.markedV s)) = ⊥)
    (hcard : Nat.card (Lv L (A5Module.markedV s) ⧸
      pCore 2 (Lv L (A5Module.markedV s))) = 3)
    (hfull : starImage (A5Module.markedZ s) (A5Module.markedV s) (Lv L (A5Module.markedV s)) =
      ⁅starImage (A5Module.markedZ s) (A5Module.markedV s) (Lv L (A5Module.markedV s)),
        starImage (A5Module.markedZ s) (A5Module.markedV s)
          (Stellmacher.elementaryAbelianMaxJ (Tv T (A5Module.markedV s)))⁆)
    (hs : (starImage (A5Module.markedZ s) (A5Module.markedV s)
      (Lv L (A5Module.markedV s))).IsSubnormal) :
    CubicHypothesis (uvRepresentation _ _ (A5Module.markedZ_mem_Gv s))
      (starImage (A5Module.markedZ s) (A5Module.markedV s) (Lv L (A5Module.markedV s)))
      (S.mapSurjective (starMk_surjective (A5Module.markedZ s) (A5Module.markedV s)))
      (starImage (A5Module.markedZ s) (A5Module.markedV s)
        (Stellmacher.elementaryAbelianMaxJ (Tv T (A5Module.markedV s)))) := by
  refine ⟨uvRepresentation_faithful _ _ _, hcore,
    Lv_star_le_offender L T _ _ _ S hS hfull, hs,
    marked_star_card_three s hcore hcard hs,
    star_sylow_normalizes L T _ _ S hS hT, ?_,
    thompson_star_le_offender T _ _ _ S hS, hfull⟩
  change ((Stellmacher.elementaryAbelianMaxJ (Tv T (A5Module.markedV s))).subgroupOf
    (Gv (A5Module.markedV s))).map (starMk _ _) ≤
      (S : Subgroup (Gv (A5Module.markedV s))).map (starMk _ _)
  apply map_mono
  have hJ : Stellmacher.elementaryAbelianMaxJ (Tv T (A5Module.markedV s)) ≤
      Tv T (A5Module.markedV s) := sSup_le fun _ h => h.1
  intro a ha
  have hm : (a : G) ∈ (S : Subgroup (Gv (A5Module.markedV s))).map
      (Gv (A5Module.markedV s)).subtype := by
    rw [hS]
    exact hJ ha
  obtain ⟨b, hb, he⟩ := hm
  have hab : b = a := Subtype.ext he
  exact hab ▸ hb

end Application
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
