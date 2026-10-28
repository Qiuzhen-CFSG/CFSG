module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.BlockOrbit
public import CFSG.Quasithin.ChapterB.Section06To07.Structure
public import Theory.GroupTheory.SylowNormalizerCommutingFamily.FactorControl
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.GroupTheory.OddSubgroupLift
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
/-!
# Odd Borel actors in the original block orbit

The commuting blocks generate O²(H). Restrict the original Sylow subgroup
there, and embed each factor's Sylow normalizer into the residual Sylow
normalizer. A natural block has a proper Sylow normalizer, so the ambient
normalizer of S ∩ O²(H) is proper and lies in the unique maximal overgroup.

The natural SL₂(2ⁿ) quotient supplies the nontrivial odd torus. Lifting it
through the two-group kernel gives an actual odd subgroup of the original
block inside that same marked maximal overgroup.

Source: Aschbacher–Smith C.5.3, printed pp.154–155, and the natural-block
case of 14.6.9, printed pp.1025–1027, using 2.4.8(5).
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
variable {H : Type*} [Group H] [Finite H]

private theorem natural_sylow_odd_actor {n : ℕ} (h : IsL2EvenBlock H n)
    (P : Sylow 2 H) :
    normalizer (P : Set H) ≠ ⊤ ∧
      ∃ D : Subgroup H, D ≤ normalizer (P : Set H) ∧ Odd (Nat.card D) ∧ D ≠ ⊥ := by
  obtain ⟨hn,_,F,_,_,hF,_,hm⟩ := h
  obtain ⟨e⟩ := hm.quotient_iso
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q : H →* SL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 H := by
    ext x
    exact e.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  have hkP : q.ker ≤ (P : Subgroup H) := hk ▸ pCore_isPGroup.le_sylow_of_normal P
  refine ⟨Matrix.SpecialLinearGroup.sylow_normalizer_ne_top_of_surjective q hq P, ?_⟩
  obtain ⟨f,hf,hker⟩ := Matrix.SpecialLinearGroup.exists_sylowNormalizer_diagonal q hq P hkP
  have hkf : IsPGroup 2 f.ker := P.isPGroup'.comap_subtype.to_le (by
    intro x hx
    exact (hker x).mp hx)
  have hbound : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  have heven : Even (Nat.card F) := by
    rw [hF,Nat.even_pow]
    exact ⟨by decide,by omega⟩
  have hodd : Odd (Nat.card (⊤ : Subgroup Fˣ)) := by
    rw [card_top,Nat.card_units]
    exact (Nat.odd_sub (by omega)).mpr (by
      simp only [show ¬ Even (1 : ℕ) by decide, iff_false]
      exact Nat.not_odd_iff_even.mpr heven)
  obtain ⟨D,_,_,hcard,_⟩ := f.exists_odd_subgroup_lift hf hkf ⊤ hodd
  refine ⟨D.map (normalizer (P : Set H)).subtype, map_subtype_le _, ?_, ?_⟩
  · rw [card_map_of_injective (normalizer (P : Set H)).subtype_injective,hcard]
    exact hodd
  · intro he
    have hd : D = ⊥ := (map_eq_bot_iff_of_injective _
      (normalizer (P : Set H)).subtype_injective).mp he
    rw [hd,card_bot,card_top,Nat.card_units] at hcard
    omega

/-- Each natural block supplies a nontrivial odd actor in the original maximal overgroup. -/
theorem OrbitDecomposition.exists_natural_odd_actor
    (S : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    {R : Subgroup H} (b : OrbitDecomposition (S : Subgroup H) R (pResidual 2 H))
    (i : Fin b.size) {n : ℕ} (hnat : IsL2EvenBlock (b.block i) n) :
    ∃ D : Subgroup H, D ≤ b.block i ∧ D ≤ ChapterB.minimalParabolicMax S hP ∧
      Odd (Nat.card D) ∧ D ≠ ⊥ := by
  let K := pResidual 2 H
  have hb (j : Fin b.size) : b.block j ≤ K :=
    (le_iSup b.block j).trans b.generate.le
  let C (j : Fin b.size) := (b.block j).subgroupOf K
  have hc : Pairwise fun j k => C j ≤ centralizer (C k : Set K) := by
    intro j k hjk x hx y hy
    apply Subtype.ext
    exact b.commute hjk hx (y : H) hy
  have hgen : iSup C = ⊤ := by
    apply map_injective K.subtype_injective
    rw [Subgroup.map_iSup]
    have hm (j : Fin b.size) : (C j).map K.subtype = b.block j :=
      map_subgroupOf_eq_of_le (hb j)
    simp_rw [hm]
    rw [b.generate, ← MonoidHom.range_eq_map, range_subtype]
  obtain ⟨P,hPS⟩ := S.exists_subgroupOf_eq_of_normal K
  let Q := (P : Subgroup K).map K.subtype
  have hQ : Q = (S : Subgroup H) ⊓ K := by
    dsimp only [Q]
    rw [hPS,subgroupOf_map_subtype]
  have hSN : (S : Subgroup H) ≤ normalizer (Q : Set H) := by
    rw [hQ]
    exact (le_inf (S : Subgroup H).le_normalizer le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨L,hL,hLN⟩ := Sylow.factor_normalizer_control C hc hgen P i
  have hnatC : IsL2EvenBlock (C i) n :=
    hnat.of_mulEquiv (subgroupOfEquivOfLe (hb i)).symm
  obtain ⟨hproper,D0,hD0,hodd,hne⟩ := natural_sylow_odd_actor hnatC L
  have hNproper : normalizer (Q : Set H) ≠ ⊤ := by
    intro he
    let : Q.Normal := normalizer_eq_top_iff.mp he
    have hPeq : (P : Subgroup K) = Q.comap K.subtype := by
      dsimp only [Q]
      rw [comap_map_eq_self_of_injective K.subtype_injective]
    have hPn : (P : Subgroup K).Normal := by
      rw [hPeq]
      infer_instance
    let := hPn
    have hLn : (L : Subgroup (C i)).Normal := by
      rw [hL]
      infer_instance
    let := hLn
    exact hproper (normalizer_eq_top _)
  have hNM : normalizer (Q : Set H) ≤ ChapterB.minimalParabolicMax S hP :=
    hP.1.le_maximal
      ⟨(ChapterB.minimalParabolicMax_spec S hP).2,
        (ChapterB.minimalParabolicMax_spec S hP).1.covBy_top⟩ hSN
      (lt_top_iff_ne_top.mpr hNproper)
  let D := (D0.map (C i).subtype).map K.subtype
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · exact (map_mono (map_subtype_le D0)).trans_eq (map_subgroupOf_eq_of_le (hb i))
  · exact ((map_mono ((map_mono hD0).trans hLN)).trans
      ((P : Subgroup K).le_normalizer_map K.subtype)).trans hNM
  · dsimp only [D]
    rwa [card_map_of_injective K.subtype_injective,
      card_map_of_injective (C i).subtype_injective]
  · intro he
    exact hne ((map_eq_bot_iff_of_injective _ (C i).subtype_injective).mp
      ((map_eq_bot_iff_of_injective _ K.subtype_injective).mp he))

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
