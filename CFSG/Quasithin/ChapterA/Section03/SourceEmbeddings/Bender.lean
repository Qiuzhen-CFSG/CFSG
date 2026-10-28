module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankOne
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Suzuki
public import Theory.GroupTheory.SylowOvergroupSolvability

/-!
# The complete Bender and binary SU₃ non-enlargement rows of A.3.12

The concrete rank-one Borel theorems place every proper full-Sylow
overgroup in its solvable Sylow normalizer. After restriction to the
containing C-component, the join with the smaller local component is
nonsolvable, hence is the whole containing component. C-component
minimality then proves equality.

This covers all three actual Bender models and the even SU₃ covering
models. It requires no quasisimplicity hypothesis on the smaller local
C-component and no embedding-list premise.
Source: Aschbacher–Smith A.3.12, pp.47–48, using F.1.3(1), pp.259–260.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open ChapterF.Source
variable {G : Type*} [Group G] [Finite G]

private theorem solvable_proper_overgroup_of_rankOne_facts
    {D : Type*} [Group D] (hfacts : ∀ S : Sylow 2 D, RankOneSylowFacts S)
    (S : Sylow 2 D) (P : Subgroup D) (hSP : (S : Subgroup D) ≤ P)
    (hne : P ≠ ⊤) : Group.IsSolvable P := by
  let := (hfacts S).solvable
  have hn := (hfacts S).unique_maximal P hSP (lt_top_iff_ne_top.mpr hne)
  exact Group.isSolvable_of_isSolvable_injective
    (f := inclusion hn) (inclusion_injective hn)

private theorem bender_solvable_proper_sylow_overgroup
    (h : ClassificationModels.IsBenderModel G) (S : Sylow 2 G) (P : Subgroup G)
    (hSP : (S : Subgroup G) ≤ P) (hne : P ≠ ⊤) : Group.IsSolvable P := by
  cases h with
  | linear n hn hm =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    exact isSolvable_proper_sylow_overgroup_of_equiv e
      (solvable_proper_overgroup_of_rankOne_facts (Linear.projective_facts F n (by omega) hF))
      S P hSP hne
  | unitary n hn hm =>
    obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hm
    exact isSolvable_proper_sylow_overgroup_of_equiv e
      (solvable_proper_overgroup_of_rankOne_facts
        (rankOneSylowFacts_psu3 J n (by omega) hF hc)) S P hSP hne
  | suzuki m _hm he =>
    obtain ⟨e⟩ := he
    exact isSolvable_proper_sylow_overgroup_of_equiv e
      (solvable_proper_overgroup_of_rankOne_facts (suzuki_rankOneSylowFacts m)) S P hSP hne

/-- No proper local C-component lies in any of the original three Bender
containing models; the full original Sylow is retained. -/
theorem eq_of_bender_containing_component
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    (hmodel : ClassificationModels.IsBenderModel L) : B = L :=
  eq_of_solvable_sylow_overgroups T hB hL hBL
    (bender_solvable_proper_sylow_overgroup hmodel)

/-- The complete A.3.12 equality alternative, including uniqueness,
for the entire Bender containing-model family. -/
theorem conclusion_of_bender_containing_component
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    (hmodel : ClassificationModels.IsBenderModel L) : Chapter1.Section02.A312Conclusion B := by
  have he := eq_of_bender_containing_component T hB hL hBL hmodel
  refine ⟨L, hL, hBL, ?_, Chapter1.Section02.A312Embedding.one he⟩
  intro D hD hBD
  exact (hL.eq_of_le hD (he ▸ hBD)).symm

/-- The actual even SU₃ covering group also has no proper local C-component.
No identification of the covering group with its projective quotient is used. -/
theorem eq_of_binary_su3_containing_component
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {n : ℕ} (hn : 0 < n) (hmodel : Chapter1.Section02.LocalModels.IsSU L 3 (2 ^ n)) :
    B = L := by
  obtain ⟨F, _, _, J, hF, hc, ⟨e⟩⟩ := hmodel
  apply eq_of_solvable_sylow_overgroups T hB hL hBL
  exact isSolvable_proper_sylow_overgroup_of_equiv e
    (solvable_proper_overgroup_of_rankOne_facts (rankOneSylowFacts_su3 J n hn hF hc))

/-- The full source conclusion on the actual even special-unitary carrier. -/
theorem conclusion_of_binary_su3_containing_component
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    {n : ℕ} (hn : 0 < n) (hmodel : Chapter1.Section02.LocalModels.IsSU L 3 (2 ^ n)) :
    Chapter1.Section02.A312Conclusion B := by
  have he := eq_of_binary_su3_containing_component T hB hL hBL hn hmodel
  refine ⟨L, hL, hBL, ?_, Chapter1.Section02.A312Embedding.one he⟩
  intro D hD hBD
  exact (hL.eq_of_le hD (he ▸ hBD)).symm

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
