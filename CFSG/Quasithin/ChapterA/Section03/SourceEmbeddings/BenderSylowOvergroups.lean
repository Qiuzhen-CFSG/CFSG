module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender
public import Theory.GroupTheory.QuasisimpleSylowOvergroup
/-!
# Bender targets normalized by a full Sylow subgroup

Every proper full-Sylow overgroup in each concrete Bender carrier is
solvable. A quasisimple subgroup normalized by that full Sylow therefore
fills the target: its join with the Sylow is nonsolvable and hence the
whole target, and quasisimplicity removes a proper normal subgroup.
Source: Aschbacher–Smith A.3.12 and 2.5.6, printed pp.47–48,554.
-/
public section
open Subgroup Theory.GroupTheory
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

theorem bender_solvable_proper_sylow_overgroup
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


theorem eq_top_of_bender (K : Subgroup G) [IsQuasisimple G] [IsQuasisimple K]
    (P : Sylow 2 G) (hn : (P : Subgroup G) ≤ normalizer (K : Set G))
    (hm : ClassificationModels.IsBenderModel G) : K=⊤ := by
  apply eq_top_of_central_image_sylow_overgroups K P hn (MonoidHom.id G) Function.surjective_id (by simp)
  intro D hPD hKD
  by_contra hD
  let : Group.IsSolvable D := bender_solvable_proper_sylow_overgroup hm P D (by simpa using hPD) hD
  have hKD' : K≤D := by simpa using hKD
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective (f := inclusion hKD') (inclusion_injective hKD')
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  exact Group.IsPerfect.not_isSolvable K inferInstance

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
