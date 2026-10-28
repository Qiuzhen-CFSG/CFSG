module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.Inputs
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.BorelRecognition
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.ModelTransport

/-!
# The fixed torus in the ambient distinguished centralizer

The subgroup used in GLS4, Chapter 2, Section 13 is the literal intersection
`Lᵤ ∩ D ∩ C_G(t)`. The local Borel recognition and the same unitary model
isomorphism identify it with the fixed part of the two-point torus. This
gives cyclicity, its exact special/projective order, oddness and nontriviality
in the original ambient group, including at q = 4. In particular it lies
in the pair stabilizer and centralizes both u and t.

Conjugacy invariance of the distinguished set gives normalization of its
distinguished centralizer by u. Identifying its centralizer inside Lᵤ,
constructing the additional linear subgroup, and identifying the fixed
group in the second centralizer are separate geometric obligations.

Source: GLS4, Chapter 2, the paragraph preceding Lemma 13.2; Chapter 4,
Lemmas 3.2 and 3.6. Both special and projective unitary covers are retained.
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion
open Subgroup Theory.GroupTheory PFchapter1section1
open _root_.BenderSuzuki.MatrixGroups RankOneModelGeometry

variable {G : Type*} [Group G] {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}

private theorem mem_right_conjugate {H : Type*} [Group H]
    (B : Subgroup H) (t x : H) :
    x ∈ rightConjugate B t ↔ t * x * t⁻¹ ∈ B := by
  rw [rightConjugate, Subgroup.conjBy, mem_map_equiv]
  simp [MulAut.conj_apply]

/-- The fixed part of the local two-point torus, as an actual subgroup of G. -/
@[expose] public def ambientFixedTorus (Z : Set G) (M : Subgroup G) (t u : G) : Subgroup G :=
  centralizerClosure Z u ⊓ residualPairStabilizer M t ⊓ centralizer ({t} : Set G)

/-- The literal local-to-ambient comparison, with the source convention
`D = M ∩ t⁻¹Mt`. No conjugacy or quotient identification is suppressed. -/
public theorem ambientFixedTorus_eq_map (htL : t ∈ centralizerClosure Z u) :
    ambientFixedTorus Z M t u =
      (twoPoint (M.comap (centralizerClosure Z u).subtype)
          (⟨t, htL⟩ : centralizerClosure Z u) ⊓
        centralizer ({⟨t, htL⟩} : Set (centralizerClosure Z u))).map
          (centralizerClosure Z u).subtype := by
  symm
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y.property, hy.1.1, ?_⟩, ?_⟩
    · exact (mem_right_conjugate M t _).mpr
        ((mem_right_conjugate (M.comap (centralizerClosure Z u).subtype)
          (⟨t, htL⟩ : centralizerClosure Z u) y).mp hy.1.2)
    · exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy.2))
  · rintro ⟨⟨hxF, hxM, hxtM⟩, hxc⟩
    refine ⟨⟨x, hxF⟩, ⟨⟨hxM, ?_⟩, ?_⟩, rfl⟩
    · exact (mem_right_conjugate (M.comap (centralizerClosure Z u).subtype)
        (⟨t, htL⟩ : centralizerClosure Z u) ⟨x, hxF⟩).mpr
          ((mem_right_conjugate M t x).mp hxtM)
    · exact mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hxc))

/-- Both ambient placements and both commuting conditions of the fixed torus. -/
public theorem ambientFixedTorus_placement :
    ambientFixedTorus Z M t u ≤ centralizerClosure Z u ∧
    ambientFixedTorus Z M t u ≤ residualPairStabilizer M t ∧
    ambientFixedTorus Z M t u ≤ centralizer ({t} : Set G) ∧
    ambientFixedTorus Z M t u ≤ centralizer ({u} : Set G) :=
  ⟨inf_le_left.trans inf_le_left, inf_le_left.trans inf_le_right,
    inf_le_right, (inf_le_left.trans inf_le_left).trans (centralizerClosure_le Z u)⟩

/-- Relative normalization follows from the literal centralization by u,
without assuming any of the second-centralizer conclusions. -/
public theorem ambientFixedTorus_second_normalizes (h : IsProductDisconnected Z M) :
    u ∈ normalizer (distinguishedCentralizer Z (ambientFixedTorus Z M t u) : Set G) := by
  have hu : u ∈ centralizer (ambientFixedTorus Z M t u : Set G) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mp (ambientFixedTorus_placement.2.2.2 hb)
  have hnorm : centralizer (ambientFixedTorus Z M t u : Set G) ≤
      normalizer (distinguishedCentralizer Z (ambientFixedTorus Z M t u) : Set G) := by
    apply le_normalizer_closure_iff.mpr
    intro g hg x hx
    exact subset_closure ⟨h.invariant g x hx.1,
      (centralizer (ambientFixedTorus Z M t u : Set G)).mul_mem
        ((centralizer (ambientFixedTorus Z M t u : Set G)).mul_mem hg hx.2)
        ((centralizer (ambientFixedTorus Z M t u : Set G)).inv_mem hg)⟩
  exact hnorm hu

private theorem fixed_torus_card_gt_one (hn : 2 ≤ n) :
    1 < (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) := by
  by_cases hn2 : n = 2
  · subst n
    decide
  · have hq : 8 ≤ 2 ^ n := Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 3 ≤ n)
    have hd : Nat.gcd 3 (2 ^ n + 1) ≤ 3 :=
      Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left _ _)
    have hdpos : 0 < Nat.gcd 3 (2 ^ n + 1) := Nat.gcd_pos_of_pos_left _ (by decide)
    have htwo : 2 ≤ (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1) :=
      (Nat.le_div_iff_mul_le hdpos).mpr (by omega)
    omega

variable [Finite G]

/-- The concrete fixed torus in any recognized unitary Borel. The exact
gcd denominator is retained, so its nontriviality is valid even at q = 4. -/
public theorem unitaryCover_borel_fixed_torus
    (hn : 2 ≤ n) (hc : IsUnitaryCentralizerCoverAt n G)
    (B : Subgroup G) (hB : IsBorelSubgroup B)
    (t : G) (ht : IsInvolution t) (htB : t ∉ B) :
    IsCyclic (twoPoint B t ⊓ centralizer ({t} : Set G) : Subgroup G) ∧
      (Nat.card (twoPoint B t ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 ^ n + 1 ∨
       Nat.card (twoPoint B t ⊓ centralizer ({t} : Set G) : Subgroup G) =
         (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) := by
  obtain ⟨_, P, rfl⟩ := hB
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, he | he⟩ := hc
  · obtain ⟨e⟩ := he
    have htor := unitary_projective_tori_of_equiv J hn hJ hcard hfixed e P t ht htB
    exact ⟨htor.2.2.2.2.2.1, Or.inr htor.2.2.2.2.2.2⟩
  · obtain ⟨e⟩ := he
    have htor := unitary_special_tori_of_equiv J hn hJ hcard hfixed e P t ht htB
    exact ⟨htor.2.2.2.2.2.1, Or.inl htor.2.2.2.2.2.2⟩

/-- Cyclicity and the exact order of the actual ambient torus. The local
Borel and its unitary model come from the supplied source alternative. -/
public theorem ambientFixedTorus_cyclic_card
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (ht : t ∈ Z) (htM : t ∉ M) (hn : 2 ≤ n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : IsInvolution u) :
    IsCyclic (ambientFixedTorus Z M t u) ∧
      (Nat.card (ambientFixedTorus Z M t u) = 2 ^ n + 1 ∨
       Nat.card (ambientFixedTorus Z M t u) = (2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) := by
  have htL : t ∈ centralizerClosure Z u := (hunitary u huD hu).1.le
    ((show zpowers t ≤ residualGenerated M z t from le_sup_right.trans le_sup_left)
      (mem_zpowers t))
  have hb := pair_involution_unitary_borel h r htM huD hu hn (hunitary u huD hu).2
  obtain ⟨hc, hcard⟩ := unitaryCover_borel_fixed_torus hn (hunitary u huD hu).2
    (M.comap (centralizerClosure Z u).subtype) hb ⟨t, htL⟩
    (IsInvolution.subtype (h.involutions t ht) htL) htM
  let B := twoPoint (M.comap (centralizerClosure Z u).subtype)
      (⟨t, htL⟩ : centralizerClosure Z u) ⊓
    centralizer ({⟨t, htL⟩} : Set (centralizerClosure Z u))
  let e := (B.equivMapOfInjective (centralizerClosure Z u).subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr (ambientFixedTorus_eq_map (M := M) htL).symm)
  refine ⟨e.isCyclic.mp hc, ?_⟩
  rwa [← Nat.card_congr e.toEquiv]

/-- The source order disjunction, oddness and nontriviality, with no
additional torus hypothesis. In the projective case the exact gcd formula
is used before weakening to the source's two permitted orders. -/
public theorem ambientFixedTorus_properties
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (ht : t ∈ Z) (htM : t ∉ M) (hn : 2 ≤ n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : IsInvolution u) :
    IsCyclic (ambientFixedTorus Z M t u) ∧
      (Nat.card (ambientFixedTorus Z M t u) = 2 ^ n + 1 ∨
       Nat.card (ambientFixedTorus Z M t u) = (2 ^ n + 1) / 3) ∧
      Odd (Nat.card (ambientFixedTorus Z M t u)) ∧ ambientFixedTorus Z M t u ≠ ⊥ := by
  obtain ⟨hc, hcard⟩ := ambientFixedTorus_cyclic_card h r ht htM hn hunitary huD hu
  have hodd : Odd (2 ^ n + 1) :=
    (even_two.pow_of_ne_zero (by omega : n ≠ 0)).add_odd odd_one
  have hgt : 1 < Nat.card (ambientFixedTorus Z M t u) := by
    rcases hcard with hcard | hcard
    · rw [hcard]
      have hp := Nat.two_pow_pos n
      omega
    · rw [hcard]
      exact fixed_torus_card_gt_one hn
  refine ⟨hc, ?_, ?_, fun he => ?_⟩
  · rcases hcard with hcard | hcard
    · exact Or.inl hcard
    · have hd := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp
        (Nat.gcd_dvd_left 3 (2 ^ n + 1))
      rcases hd with hd | hd
      · exact Or.inl (by simpa [hd] using hcard)
      · exact Or.inr (by simpa [hd] using hcard)
  · rcases hcard with hcard | hcard
    · exact hcard ▸ hodd
    · rw [hcard]
      exact hodd.of_dvd_nat (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right 3 _))
  · rw [he, card_bot] at hgt
    omega

end BenderSuzuki.ZD.UnitaryExclusion
