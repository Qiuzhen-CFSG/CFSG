module
public import Theory.GroupTheory.CComponent.StrictSectionSmallImage
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupTheory.SylowNormalizerOvergroup
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoMathieu

/-!
# Small elementary actions of strict local PSL₃(2) extensions

The automorphism group of an elementary binary group of order at most
eight has order at most 168. In a strict chain A < B of local components
normalized by the original full Sylow, the two-core of B normalizes A.
If A/O₂(A) is PSL₃(2) and B/O₂(B) is quasisimple, small-image rigidity
therefore makes B fix the elementary subgroup pointwise. This is used
on the pure normal-elementary rows of the native J₄ catalogue.

Source: Aschbacher--Smith 12.9.3, printed pp.858--859, using A.3.3
and the native Sylow normal-elementary catalogue.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoMathieu
open FiveLocalFF.SolvableQuotients

private theorem aut_card_le {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hE : Nat.card E ≤ 8) : Nat.card (MulAut E) ≤ 168 := by
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by simpa [←hk] using hE)
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E k hk]
  interval_cases k <;> norm_num [Fin.prod_univ_succ]

/-- A strict extension of a local PSL3(2) section fixes every common invariant
elementary two-subgroup of order at most eight. -/
theorem strict_three_centralizes_small {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {A B E : Subgroup G}
    (ha : A ∈ localCComponents S) (hb : B ∈ localCComponents S) (hlt : A < B)
    (hna : (S : Subgroup G) ≤ normalizer (A : Set G))
    (hnb : (S : Subgroup G) ≤ normalizer (B : Set G))
    (ha3 : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 2)
    (hquasi : IsQuasisimple (B ⧸ pCore 2 B))
    (hE : IsElementaryAbelian 2 E) (hc : Nat.card E ≤ 8)
    (hBE : B ≤ normalizer (E : Set G)) : B ≤ centralizer (E : Set G) := by
  let H := B ⊔ (S : Subgroup G)
  have hBH : B ≤ H := le_sup_left
  have hAH : A ≤ H := hlt.le.trans hBH
  let A' := A.subgroupOf H
  let B' := B.subgroupOf H
  let dA := subgroupOfEquivOfLe hAH
  let dB := subgroupOfEquivOfLe hBH
  let a := QuotientGroup.congr _ _ dA (pCore_map_iso 2 dA)
  let b := QuotientGroup.congr _ _ dB (pCore_map_iso 2 dB)
  let := local_perfect ha
  let : Group.IsPerfect A' := Group.IsPerfect.ofSurjective
    (f := dA.symm.toMonoidHom) dA.symm.surjective
  have hsimple : IsSimpleGroup (A ⧸ pCore 2 A) := by
    obtain ⟨k,_,_,_,⟨e⟩⟩ := ha3
    let := Atlas.psl_simple_high_rank (F := k) 3 (by decide)
    exact e.isSimpleGroup
  let : IsSimpleGroup (A' ⧸ pCore 2 A') := a.isSimpleGroup
  let : IsQuasisimple (B' ⧸ pCore 2 B') := hquasi.of_mulEquiv b.symm
  have hlt' : A' < B' := by
    refine lt_of_le_of_ne (comap_mono hlt.le) ?_
    intro he
    apply hlt.ne
    have he' := congrArg (map H.subtype) he
    simpa only [A',B',map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le hBH] using he'
  have hcoreS : B.pCoreIn 2 ≤ (S : Subgroup G) :=
    (pCore_isPGroup.map B.subtype).le_sylow_of_normalized S
      (hnb.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
  have hn : pCore 2 B' ≤ normalizer (A'.subgroupOf B' : Set B') := by
    intro z hz
    have hzB : dB z ∈ pCore 2 B := by
      rw [←pCore_map_iso 2 dB]
      exact mem_map_of_mem _ hz
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hna (hcoreS (mem_map_of_mem B.subtype hzB))) (x : G)
  let := hE
  let f := (E.normalizerMonoidHom.comp (inclusion hBE)).comp dB.toMonoidHom
  have hcard : Nat.card (A' ⧸ pCore 2 A') = 168 := by
    rw [Nat.card_congr a.toEquiv]
    obtain ⟨k,_,_,hk,⟨e⟩⟩ := ha3
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hk]
    norm_num
  have hf := Theory.GroupTheory.IsCComponent.hom_eq_one_of_strict_simple_section hb hlt' hn f (by
    rw [hcard]
    exact aut_card_le hc)
  intro z hz
  have hk : inclusion hBE ⟨z,hz⟩ ∈ E.normalizerMonoidHom.ker := by
    change f (dB.symm ⟨z,hz⟩) = 1
    rw [hf]
    rfl
  rwa [normalizerMonoidHom_ker] at hk
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoMathieu
