module

public import CFSG.Quasithin.ChapterF.Section01.SourceLocalSylow
public import CFSG.Quasithin.ChapterF.Section01.SourceFaithfulTriple
public import Theory.GroupTheory.SelfCentralizingCoreNormalExtension

/-!
# The mixed F.1.1 pair in the 6.1.5 continuation

The source continuation uses the two local groups `L S` and `K₁ S`, where
`S = Baum(T)` and `D` is the odd Hall subgroup of `N_L(T ∩ L)`.  The right
local quotient is cubic, so its source Borel is just `S`; the left Borel is
the displayed `S D`.  This file isolates exactly the remaining local inputs
and constructs the genuine source `HypothesisF11` record.  No weak-BN or
F.1.12 conclusion is assumed here.

Source: Aschbacher--Smith 6.1.5, printed pp.667--668, and F.1.1/F.1.9,
printed pp.259--262 (`refs/quasithin.pdf`).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Literal local data for the mixed pair `(L S, K₁ S)`.

The subgroup fields `L` and `K` denote the full local groups `L S` and
`K₁ S`. Their source Borels are `S D` and `S`, respectively. The two
characteristic-two equalities concern the actual parabolics `L` and
`K ⊔ D`; normalization of `K` by `D` does not imply `D ≤ K`.
-/
structure MixedF11Data where
  L : Subgroup G
  K : Subgroup G
  S : Subgroup G
  D : Subgroup G
  finite_S : Finite S
  S_isP : IsPGroup 2 S
  S_le_L : S ≤ L
  S_le_K : S ≤ K
  D_normalizes_K : D ≤ normalizer (K : Set G)
  left_borel : ChapterF.Source.borel L S = S ⊔ D
  right_borel : ChapterF.Source.borel K S = S
  sylow_L : Chapter1.IsSylowIn 2 S L
  sylow_K : Chapter1.IsSylowIn 2 S K
  left_quotient : ChapterF.Source.IsRankOneModel (L ⧸ pCore 2 L)
  right_quotient : ChapterF.Source.IsRankOneModel (K ⧸ pCore 2 K)
  core_free : pCore 2 (L ⊔ K ⊔ S : Subgroup G) = ⊥
  characteristic_L : generalizedFitting (L : Subgroup G) = pCore 2 (L : Subgroup G)
  characteristic_one :
    generalizedFitting (K ⊔ D : Subgroup G) = pCore 2 (K ⊔ D : Subgroup G)

/-- The source Borel identities and a faithful central seed make the enlarged
right parabolic characteristic two. -/
theorem mixed_right_characteristic_two_of_faithful_seed
    (L K S D Z : Subgroup G) (hS : IsPGroup 2 S)
    (hSL : S ≤ L) (hSK : S ≤ K) (hDK : D ≤ normalizer (K : Set G))
    (hleft : ChapterF.Source.borel L S = S ⊔ D)
    (hright : ChapterF.Source.borel K S = S)
    (hK : generalizedFitting K = pCore 2 K)
    (hZS : Z ≤ S) (hSZ : S ≤ centralizer (Z : Set G))
    (hfaith : D ⊓ centralizer (Z : Set G) = ⊥) :
    generalizedFitting (K ⊔ D : Subgroup G) = pCore 2 (K ⊔ D : Subgroup G) := by
  have hDS : D ≤ normalizer (S : Set G) := by
    apply le_trans le_sup_right
    rw [← hleft]
    unfold ChapterF.Source.borel
    rw [inf_eq_left.mpr hSL]
    exact inf_le_right
  have hB : K ⊓ normalizer (S : Set G) = S := by
    simpa only [ChapterF.Source.borel, inf_eq_left.mpr hSK] using hright
  exact (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
    (Subgroup.core_selfCentralizing_sup_of_faithful_seed K S D Z
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hK) hS hSK hDK hDS hB hZS hSZ hfaith)

/-- Construct the mixed source data from a characteristic-two `K₁ S` and the
faithful Hall action on a central seed. The characteristic-two condition on
`K₁ D S` is a conclusion of the preceding normal-extension theorem. -/
def MixedF11Data.ofFaithfulSeed
    (L K S D Z : Subgroup G) (hDK : D ≤ normalizer (K : Set G))
    (hleft : ChapterF.Source.borel L S = S ⊔ D)
    (hright : ChapterF.Source.borel K S = S)
    (hSylL : Chapter1.IsSylowIn 2 S L) (hSylK : Chapter1.IsSylowIn 2 S K)
    (hQL : ChapterF.Source.IsRankOneModel (L ⧸ pCore 2 L))
    (hQK : ChapterF.Source.IsRankOneModel (K ⧸ pCore 2 K))
    (hcore : pCore 2 (L ⊔ K ⊔ S : Subgroup G) = ⊥)
    (hL : generalizedFitting L = pCore 2 L)
    (hK : generalizedFitting K = pCore 2 K)
    (hZS : Z ≤ S) (hSZ : S ≤ centralizer (Z : Set G))
    (hfaith : D ⊓ centralizer (Z : Set G) = ⊥) : MixedF11Data (G := G) where
  L := L
  K := K
  S := S
  D := D
  finite_S := inferInstance
  S_isP := (Chapter1.isSylowIn_iff.mp hSylL).1
  S_le_L := (Chapter1.isSylowIn_iff.mp hSylL).2.1
  S_le_K := (Chapter1.isSylowIn_iff.mp hSylK).2.1
  D_normalizes_K := hDK
  left_borel := hleft
  right_borel := hright
  sylow_L := hSylL
  sylow_K := hSylK
  left_quotient := hQL
  right_quotient := hQK
  core_free := hcore
  characteristic_L := hL
  characteristic_one := mixed_right_characteristic_two_of_faithful_seed L K S D Z
    (Chapter1.isSylowIn_iff.mp hSylL).1 (Chapter1.isSylowIn_iff.mp hSylL).2.1
    (Chapter1.isSylowIn_iff.mp hSylK).2.1 hDK hleft hright hK hZS hSZ hfaith

omit [Finite G] in
private theorem parabolic_zero (d : MixedF11Data (G := G)) :
    ChapterF.Source.parabolic (fun i : Fin 2 => ![d.L, d.K] i) d.S (0 : Fin 2) = d.L := by
  change d.L ⊔ d.S ⊔ ChapterF.Source.borel d.K d.S = d.L
  rw [d.right_borel, sup_eq_left.mpr d.S_le_L, sup_eq_left.mpr d.S_le_L]

omit [Finite G] in
private theorem parabolic_one (d : MixedF11Data (G := G)) :
    ChapterF.Source.parabolic (fun i : Fin 2 => ![d.L, d.K] i) d.S (1 : Fin 2) =
      d.K ⊔ d.D := by
  change d.K ⊔ d.S ⊔ ChapterF.Source.borel d.L d.S = d.K ⊔ d.D
  rw [d.left_borel]
  rw [sup_eq_left.mpr d.S_le_K, ← sup_assoc, sup_eq_left.mpr d.S_le_K]

omit [Finite G] in
private theorem cross_left (d : MixedF11Data (G := G)) :
    ChapterF.Source.borel d.K d.S ≤ normalizer (d.L : Set G) := by
  rw [d.right_borel]
  exact d.S_le_L.trans Subgroup.le_normalizer

omit [Finite G] in
private theorem cross_right (d : MixedF11Data (G := G)) :
    ChapterF.Source.borel d.L d.S ≤ normalizer (d.K : Set G) := by
  rw [d.left_borel]
  exact sup_le (d.S_le_K.trans Subgroup.le_normalizer) d.D_normalizes_K

omit [Finite G] in
/-- The actual six-clause source F.1.1 record for `L S` and `K₁ S`. -/
theorem MixedF11Data.hypothesisF11 (d : MixedF11Data (G := G)) :
    ChapterF.Source.HypothesisF11 (fun i : Fin 2 => ![d.L, d.K] i) d.S := by
  have hSN : ∀ i : Fin 2, d.S ≤ normalizer ((![d.L, d.K] i : Subgroup G) : Set G) := by
    intro i
    fin_cases i
    · exact d.S_le_L.trans Subgroup.le_normalizer
    · exact d.S_le_K.trans Subgroup.le_normalizer
  have hSyl : ∀ i : Fin 2, ∃ P : Sylow 2 (![d.L, d.K] i),
      (P : Subgroup (![d.L, d.K] i)).map (![d.L, d.K] i).subtype =
        d.S ⊓ (![d.L, d.K] i) := by
    intro i
    fin_cases i
    · change ∃ P : Sylow 2 d.L,
        (P : Subgroup d.L).map d.L.subtype = d.S ⊓ d.L
      obtain ⟨P, hP⟩ := d.sylow_L
      exact ⟨P, hP.trans (inf_eq_left.mpr d.S_le_L).symm⟩
    · change ∃ P : Sylow 2 d.K,
        (P : Subgroup d.K).map d.K.subtype = d.S ⊓ d.K
      obtain ⟨P, hP⟩ := d.sylow_K
      exact ⟨P, hP.trans (inf_eq_left.mpr d.S_le_K).symm⟩
  have hQ : ∀ i : Fin 2,
      ChapterF.Source.IsRankOneModel ((![d.L, d.K] i) ⧸
        pCore 2 (![d.L, d.K] i)) := by
    intro i
    fin_cases i
    · exact d.left_quotient
    · exact d.right_quotient
  have hchar : ∀ i : Fin 2,
      generalizedFitting
          (ChapterF.Source.parabolic (fun j : Fin 2 => ![d.L, d.K] j) d.S i) =
        pCore 2 (ChapterF.Source.parabolic (fun j : Fin 2 => ![d.L, d.K] j) d.S i) := by
    intro i
    fin_cases i
    · change generalizedFitting
          (ChapterF.Source.parabolic (fun j : Fin 2 => ![d.L, d.K] j) d.S (0 : Fin 2) :
            Subgroup G) =
        pCore 2 (ChapterF.Source.parabolic
          (fun j : Fin 2 => ![d.L, d.K] j) d.S (0 : Fin 2) : Subgroup G)
      rw [parabolic_zero d]
      exact d.characteristic_L
    · change generalizedFitting
          (d.K ⊔ d.S ⊔ ChapterF.Source.borel d.L d.S : Subgroup G) =
        pCore 2 (d.K ⊔ d.S ⊔ ChapterF.Source.borel d.L d.S : Subgroup G)
      rw [d.left_borel]
      have hKD : d.K ⊔ d.S ⊔ (d.S ⊔ d.D : Subgroup G) = d.K ⊔ d.D := by
        rw [sup_eq_left.mpr d.S_le_K, ← sup_assoc, sup_eq_left.mpr d.S_le_K]
      rw [hKD]
      exact d.characteristic_one
  refine ⟨d.finite_S, d.S_isP, hSN, hSyl, hQ, ?_, ?_, hchar⟩
  · intro i
    fin_cases i
    · change ChapterF.Source.borel d.K d.S ≤ normalizer (d.L : Set G)
      exact cross_left d
    · change ChapterF.Source.borel d.L d.S ≤ normalizer (d.K : Set G)
      exact cross_right d
  · change pCore 2 (d.L ⊔ d.K ⊔ d.S : Subgroup G) = ⊥
    exact d.core_free

omit [Finite G] in
/-- F.1.9 on the literal generated mixed completion. -/
theorem MixedF11Data.faithfulTriple (d : MixedF11Data (G := G)) :
    ChapterF.Source.LocallyRankOneTriple
      (fun i => (ChapterF.Source.parabolic (fun j : Fin 2 => ![d.L, d.K] j) d.S i).subgroupOf
        (ChapterF.Source.generated (fun j : Fin 2 => ![d.L, d.K] j) d.S))
      ((ChapterF.Source.commonBorel (fun j : Fin 2 => ![d.L, d.K] j) d.S).subgroupOf
        (ChapterF.Source.generated (fun j : Fin 2 => ![d.L, d.K] j) d.S)) :=
  (d.hypothesisF11).generatedLocallyRankOneTriple

omit [Finite G] in
/-- The source local groups and their literal overlap and completion. -/
theorem MixedF11Data.literalParabolics (d : MixedF11Data (G := G)) :
    ChapterF.Source.parabolic (fun i : Fin 2 => ![d.L, d.K] i) d.S (0 : Fin 2) = d.L ∧
    ChapterF.Source.parabolic (fun i : Fin 2 => ![d.L, d.K] i) d.S (1 : Fin 2) =
      d.K ⊔ d.D ∧
    ChapterF.Source.commonBorel (fun i : Fin 2 => ![d.L, d.K] i) d.S = d.S ⊔ d.D ∧
    ChapterF.Source.generated (fun i : Fin 2 => ![d.L, d.K] i) d.S = d.L ⊔ d.K := by
  refine ⟨parabolic_zero d, parabolic_one d, ?_, ?_⟩
  · unfold ChapterF.Source.commonBorel
    change ChapterF.Source.borel d.L d.S ⊔ ChapterF.Source.borel d.K d.S ⊔ d.S =
      d.S ⊔ d.D
    rw [d.right_borel, d.left_borel]
    have hS : d.S ≤ d.S ⊔ d.D := le_sup_left
    rw [sup_eq_left.mpr hS, sup_eq_left.mpr hS]
  · unfold ChapterF.Source.generated
    change d.L ⊔ d.K ⊔ d.S = d.L ⊔ d.K
    exact sup_eq_left.mpr (d.S_le_L.trans le_sup_left)

omit [Finite G] in
/-- F.1.9 applied to `L S` and `K₁ D S`, with overlap `S D` in `⟨L,K₁,S⟩`.
The remaining rank-two recognition is independent of this local construction. -/
theorem MixedF11Data.literalFaithfulTriple (d : MixedF11Data (G := G)) :
    ChapterF.Source.LocallyRankOneTriple
      (fun i => (![d.L, d.K ⊔ d.D] i).subgroupOf (d.L ⊔ d.K))
      ((d.S ⊔ d.D).subgroupOf (d.L ⊔ d.K)) := by
  have h := d.faithfulTriple
  have hlit := d.literalParabolics
  rcases hlit with ⟨h0, h1, hb, hg⟩
  rw [← hg, ← hb]
  convert h using 1
  · funext i
    fin_cases i
    · change d.L.subgroupOf (ChapterF.Source.generated
          (fun j : Fin 2 => ![d.L, d.K] j) d.S) =
        (ChapterF.Source.parabolic (fun j : Fin 2 => ![d.L, d.K] j) d.S (0 : Fin 2)).subgroupOf
          (ChapterF.Source.generated (fun j : Fin 2 => ![d.L, d.K] j) d.S)
      rw [h0]
    · change (d.K ⊔ d.D).subgroupOf (ChapterF.Source.generated
          (fun j : Fin 2 => ![d.L, d.K] j) d.S) =
        (ChapterF.Source.parabolic (fun j : Fin 2 => ![d.L, d.K] j) d.S (1 : Fin 2)).subgroupOf
          (ChapterF.Source.generated (fun j : Fin 2 => ![d.L, d.K] j) d.S)
      rw [h1]

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
