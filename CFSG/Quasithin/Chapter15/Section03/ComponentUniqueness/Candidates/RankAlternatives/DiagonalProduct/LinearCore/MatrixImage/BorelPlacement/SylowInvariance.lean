module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage.BorelPlacement
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage.BorelPlacement.Orientation
public import Theory.GroupAction.SolvableSylowInvariance
public import Theory.GroupTheory.SolvableNormalSup
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups

/-!
# Transport of the full local action to the actual component Sylow

The two-core quotient makes Y₊ solvable, and the actual construction of S
makes it normalize Y₊. Thus Y₊S is solvable. Its quotient action contains
the inner image of the entire component Sylow. The general solvable-action
lemma therefore reduces full invariance to the intrinsic statement that a
solvable overgroup of a Sylow subgroup of PSL₃(F) normalizes that Sylow.
The full preimage identity then lifts invariance to the original S ∩ L.

Both source interfaces use the same transfer theorem. The intrinsic matrix
theorem discharges its solvable-overgroup premise for every positive even
exponent, including the field of order four. All quotient maps and component
Sylows are the supplied ones, including for central covers. The full Y₊S
action preserves S ∩ L; no product decomposition of Y₊ or exponent claim
about Y₊ itself is needed.

Source: Aschbacher--Smith, 15.3.11--12, 15.3.36--38, especially printed
pp.1135--1136 of the combined manuscript (1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.MatrixImage
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A solvable action containing the inner Sylow image preserves its literal
preimage once the intrinsic solvable-overgroup normalizer criterion holds. -/
theorem sylow_preimage_invariant_of_solvable_overgroups
    {A S L : Subgroup G} (hsol : Group.IsSolvable A)
    (hn : A ≤ normalizer (L : Set G)) (hSA : S ≤ A)
    {K : Type*} [Group K] [Finite K] (e : (L ⧸ pCore 2 L) ≃* K)
    (P : Sylow 2 K)
    (hP : (P : Subgroup K) = (S.subgroupOf L).map (quotientMap e))
    (hpre : (P : Subgroup K).comap (quotientMap e) = S.subgroupOf L)
    (hmodel : ∀ H : Subgroup K, Group.IsSolvable H →
      (P : Subgroup K) ≤ H → H ≤ normalizer (P : Set K)) :
    A ≤ normalizer (S ⊓ L : Subgroup G) := by
  let f := quotientAction hn e
  let := hsol
  let : Group.IsSolvable f.range := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hinner : (P : Subgroup K).map MulAut.conj ≤ f.range := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hP] at hx
    obtain ⟨l, hl, rfl⟩ := hx
    refine ⟨⟨l, hSA hl⟩, ?_⟩
    exact quotientAction_on_component hn e _ l.property
  have hinv (a : A) : (P : Subgroup K).map (f a).toMonoidHom = P :=
    MulAut.sylow_map_eq_of_solvable_overgroups P hmodel f.range hinner (f a) ⟨a, rfl⟩
  apply le_normalizer_iff.mpr
  rintro a ha l ⟨hlS, hlL⟩
  let a' : A := ⟨a, ha⟩
  let l' : L := ⟨l, hlL⟩
  let al := L.normalizerMonoidHom ⟨a, hn ha⟩ l'
  have hlP : quotientMap e l' ∈ (P : Subgroup K) := by
    change l' ∈ (P : Subgroup K).comap (quotientMap e)
    rw [hpre]
    exact hlS
  have hal : quotientMap e al ∈ (P : Subgroup K) := by
    have hm := mem_map_of_mem (f a').toMonoidHom hlP
    rw [hinv a'] at hm
    change quotientAction hn e a' (e (QuotientGroup.mk' _ l')) ∈ _ at hm
    rw [quotientAction_apply] at hm
    exact hm
  have halS : (al : G) ∈ S := by
    change al ∈ S.subgroupOf L
    rw [← hpre]
    exact hal
  exact ⟨halS, al.property⟩

variable {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}

/-- The genuine two-core quotient and S-invariance give solvability of Y₊S. -/
theorem SourceSetup.local_solvable (h : SourceSetup d I L) :
    Group.IsSolvable (d.Yplus ⊔ d.S : Subgroup G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let := (pCore_isPGroup (p := 2) (G := d.Yplus)).isNilpotent
  let := h.yplus_quotient_three.isNilpotent
  let : Group.IsSolvable d.Yplus :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 d.Yplus)).mpr
      ⟨inferInstance, inferInstance⟩
  let := (d.T.isPGroup'.to_le (show d.S ≤ (d.T : Subgroup G) from inf_le_left)).isNilpotent
  let H := d.Yplus ⊔ d.S
  let : (d.Yplus.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le d.Yplus.le_normalizer
      (RankTwo.planeStabilizer_normalizes_yplus d.action d.T d.sylow_le 1 d.choice))
  let : Group.IsSolvable (d.Yplus.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show d.Yplus ≤ H from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show d.Yplus ≤ H from le_sup_left)).injective
  let : Group.IsSolvable (d.S.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show d.S ≤ H from le_sup_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show d.S ≤ H from le_sup_right)).injective
  exact Group.isSolvable_of_normal_sup_eq_top _ _ (codisjoint_subgroupOf_sup d.Yplus d.S).eq_top

/-- The first source interface, reduced to one intrinsic PSL₃ calculation.
This proves preservation by all of Y₊S, retaining the given quotient coordinates. -/
theorem SourceSetup.component_sylow_invariant_of_solvable_overgroups
    (h : SourceSetup d I L) (hn : d.Yplus ≤ normalizer (L : Set G))
    {F : Type*} [Field F] [Finite F] (e : (L ⧸ pCore 2 L) ≃* PSL(3,F))
    (hmodel : ∀ P : Sylow 2 PSL(3,F), ∀ H : Subgroup PSL(3,F),
      Group.IsSolvable H → (P : Subgroup PSL(3,F)) ≤ H →
        H ≤ normalizer (P : Set PSL(3,F))) :
    d.Yplus ⊔ d.S ≤ normalizer (d.S ⊓ L : Subgroup G) := by
  have hSL : d.S ≤ normalizer (L : Set G) := by
    simpa only [← h.orbit_eq] using le_normalizer_conjugateSpanBy L d.S
  obtain ⟨P, hP⟩ := h.quotient_sylow e
  exact sylow_preimage_invariant_of_solvable_overgroups h.local_solvable
    (sup_le hn hSL) le_sup_right e P hP (h.sylow_preimage e P hP) (hmodel P)

/-- The full local group preserves the actual component Sylow in every
supplied projective quotient of positive even exponent. -/
theorem SourceSetup.component_sylow_invariant_of_even_card
    (h : SourceSetup d I L) (hn : d.Yplus ≤ normalizer (L : Set G))
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hnpos : 0 < n) (heven : Even n) (hcard : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* PSL(3,F)) :
    d.Yplus ⊔ d.S ≤ normalizer (d.S ⊓ L : Subgroup G) :=
  h.component_sylow_invariant_of_solvable_overgroups hn e
    (Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer
      F hnpos heven hcard)

/-- The invariance premise of `borelPlacement_of_sylow_invariant`, in the
original actor's coordinates. Both the ordinary and central-cover cases apply. -/
theorem SourceSetup.component_sylow_invariant
    (h : SourceSetup d I L) (hn : d.Yplus ≤ normalizer (L : Set G))
    (y : d.Yplus) (_hy : orderOf y = 3)
    {F : Type*} [Field F] [Finite F] (hcase : LinearCase L (Nat.card F))
    (w : DiagonalCoordinates L (y : G) F) :
    d.Yplus ≤ normalizer (d.S ⊓ L : Subgroup G) := by
  obtain ⟨n, hnpos, heven, hcard⟩ := hcase.even_card
  exact le_sup_left.trans
    (h.component_sylow_invariant_of_even_card hn hnpos heven hcard w.e)

end CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.MatrixImage

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel
variable {G : Type*} [Group G] [Finite G]
variable {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}

/-- The oriented-Borel interface uses the same full-action argument and
lifts through the entire two-kernel in the original projective marking. -/
theorem Setup.component_sylow_invariant_of_solvable_overgroups
    (h : Setup d I L) (e : Earlier d) {q : ℕ} (c : ProjectiveMarking L q)
    (hmodel : ∀ P : Sylow 2 PSL(3,c.F), ∀ H : Subgroup PSL(3,c.F),
      Group.IsSolvable H → (P : Subgroup PSL(3,c.F)) ≤ H →
        H ≤ normalizer (P : Set PSL(3,c.F))) :
    d.Yplus ⊔ d.S ≤ normalizer (d.S ⊓ L : Subgroup G) := by
  obtain ⟨P, hP, hpre⟩ := h.projective_sylow e c
  have hpre' : (P : Subgroup PSL(3,c.F)).comap
      (Candidates.LinearCore.MatrixImage.quotientMap c.equivalence) = d.S.subgroupOf L := by
    ext l
    change projectiveMap c l ∈ (P : Subgroup PSL(3,c.F)) ↔ (l : G) ∈ d.S
    constructor
    · intro hl
      have hm : (l : G) ∈ projectivePreimage c P := mem_map_of_mem L.subtype hl
      exact (hpre ▸ hm).1
    · intro hl
      have hm : (l : G) ∈ projectivePreimage c P := hpre.symm ▸ ⟨hl, l.property⟩
      obtain ⟨l', hl', he⟩ := hm
      have he' : l' = l := Subtype.ext he
      exact he' ▸ hl'
  exact Candidates.LinearCore.MatrixImage.sylow_preimage_invariant_of_solvable_overgroups
    e.solvable (h.outside.1.2.trans (h.normalizes_component e)) le_sup_right
    c.equivalence P hP.symm hpre' (hmodel P)

/-- Full local invariance in the original projective marking, including the
central two-cover case. The selected diagonal actor needs no extra restriction. -/
theorem Setup.component_sylow_invariant
    (h : Setup d I L) (e : Earlier d) {n : ℕ}
    (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n)) :
    d.Yplus ⊔ d.S ≤ normalizer (d.S ⊓ L : Subgroup G) :=
  h.component_sylow_invariant_of_solvable_overgroups e c
    (Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_overgroup_le_normalizer
      c.F hn heven c.card)

/-- Discharge precisely the Sylow-invariance premise of
`orientedBorelData_of_marked_local` using its original marked actor. -/
theorem component_sylow_invariant_of_marked_local
    (hI : I ∈ d.Hplus) (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hrL : primeRank 3 L = 2) (hrY : primeRank 3 d.Yplus = 2) (e : Earlier d)
    {n : ℕ} (hn : 0 < n) (heven : Even n) (c : ProjectiveMarking L (2 ^ n))
    {y : G} (hy : y ∈ d.Yplus) (hdiag : c.Diagonal y) :
    d.Yplus ⊔ d.S ≤ normalizer (d.S ⊓ L : Subgroup G) :=
  (setup_of_marked_actor hI hLI hL hrL hrY c hy hdiag).component_sylow_invariant
    e hn heven c

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover.SourceBorel
