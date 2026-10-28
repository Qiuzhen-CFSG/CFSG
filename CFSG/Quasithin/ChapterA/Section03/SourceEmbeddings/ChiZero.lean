module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankOne
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.SylowOvergroupSolvability
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups

/-!
# No proper local C-component in a χ₀ containing block

The three original χ₀ models all have solvable proper Sylow overgroups.
The rank-one calculation treats SL₂ in characteristic two; every proper
subgroup of A₅ is solvable; A₃ itself is solvable. Each assertion lifts
through the literal two-core quotient specified by the block model.

The full ambient Sylow then forces any contained local C-component to equal
the containing C-component. This is the non-enlargement use of A.3.12 in
2.4.6, without requiring the unrelated proper sporadic embedding catalogue.
The quotient corollary records the original ambient quotient map explicitly.

Source: Aschbacher–Smith 2.4.6, printed p.528, using C.1.12 and A.3.12.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
universe u
variable {G : Type u} [Group G] [Finite G]

/-- All three genuine χ₀ models have solvable proper full-Sylow overgroups. -/
theorem chiZero_isSolvable_proper_sylow_overgroup
    (h : ChapterC.IsChiZeroBlock G) (S : Sylow 2 G) (P : Subgroup G)
    (hSP : (S : Subgroup G) ≤ P) (hne : P ≠ ⊤) : Group.IsSolvable P := by
  apply isSolvable_proper_sylow_overgroup_of_twoCore_quotient ?_ S P hSP hne
  intro T D hTD hD
  rcases h with ⟨n, hn, _, F, _, _, hF, _, hmodel⟩ | h | h
  · let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    obtain ⟨e⟩ := hmodel.quotient_iso
    exact isSolvable_proper_sylow_overgroup_of_equiv e
      Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup T D hTD hD
  · obtain ⟨e⟩ := h.2.2.quotient_iso
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
    let : Group.IsSolvable (G ⧸ pCore 2 G) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    infer_instance
  · obtain ⟨e⟩ := h.2.2.quotient_iso
    exact alternatingGroup.isSolvable_subgroup_of_equiv_five e D hD

/-- A.3.12's first alternative for an actual containing χ₀ C-component.
No invariance premise on the smaller local component is needed. -/
theorem eq_of_chiZero_containing_component
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    (hmodel : ChapterC.IsChiZeroBlock L) : B = L :=
  eq_of_solvable_sylow_overgroups T hB hL hBL
    (chiZero_isSolvable_proper_sylow_overgroup hmodel)

/-- The full A.3.12 conclusion in the χ₀ containing-component branch. -/
theorem conclusion_of_chiZero_containing_component
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    (hmodel : ChapterC.IsChiZeroBlock L) : Chapter1.Section02.A312Conclusion B := by
  have he := eq_of_chiZero_containing_component T hB hL hBL hmodel
  refine ⟨L, hL, hBL, ?_, Chapter1.Section02.A312Embedding.one he⟩
  intro D hD hBD
  exact (hL.eq_of_le hD (he ▸ hBD)).symm

/-- The literal quotient conclusion for the Chapter 2 local family. In this
case the original source inclusions also prove equality before quotienting. -/
theorem local_twoCore_images_eq_of_chiZero_containing_component
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ Chapter1.L G T) (hL : L.IsCComponent) (hBL : B ≤ L)
    (hmodel : ChapterC.IsChiZeroBlock L) :
    B.map (QuotientGroup.mk' (pCore 2 G)) =
      L.map (QuotientGroup.mk' (pCore 2 G)) := by
  rw [eq_of_chiZero_containing_component T hB.1 hL hBL hmodel]

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
