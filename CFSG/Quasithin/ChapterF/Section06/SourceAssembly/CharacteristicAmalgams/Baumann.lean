module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.CentralReduction
public import Stellmacher.BaumannIntermediate
public import Stellmacher.BaumannNormalizer
public import Stellmacher.OmegaOneCenterMap

/-!
# A Baumann subgroup cannot lie in both Goldschmidt cores

Baumann heredity identifies B(T) with B(Qᵢ) whenever B(T)≤Qᵢ≤T.
Since Qᵢ is normal in its vertex, this makes B(T) normal there. If both
containments held, the faithful-amalgam condition would kill B(T), and
therefore its nontrivial Sylow omega-center. Thus a core containment on
one side supplies the noncontainment on the other.

Source: Aschbacher–Smith F.6.3–F.6.5, with the elementary Baumann heredity
used in Stellmacher (6.1), Journal of Algebra 190 (1997), p.30.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Stellmacher.SectionsFiveToSeven
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

private theorem vertex_normalizes_baumann_of_le_core
    (h : IsGoldschmidtTriple G₁ G₂)
    (hB : baumannIn (G₁ ⊓ G₂) ≤ (pCore 2 G₁).map G₁.subtype) :
    G₁ ≤ normalizer (baumannIn (G₁ ⊓ G₂) : Set G) := by
  let Q := (pCore 2 G₁).map G₁.subtype
  have hQT : Q ≤ G₁ ⊓ G₂ := h.local_twoCore_le_intersection
  have he : baumannIn Q = baumannIn (G₁ ⊓ G₂) :=
    baumann_eq_of_intermediate (G₁ ⊓ G₂) Q hB hQT
  have hQP : Q ≤ G₁ := map_subtype_le _
  have hQn : (Q.subgroupOf G₁).Normal := by
    change (((pCore 2 G₁).map G₁.subtype).subgroupOf G₁).Normal
    rw [subgroupOf_map_subtype_eq]
    infer_instance
  have hh := ((normal_subgroupOf_iff_le_normalizer hQP).mp hQn).trans
    (normalizer_le_normalizer_baumann Q)
  change G₁ ≤ normalizer (baumannIn Q : Set G) at hh
  rwa [he] at hh

/-- The Baumann subgroup of the actual overlap escapes at least one vertex core. -/
theorem IsGoldschmidtTriple.baumann_not_le_both_cores
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥) :
    ¬ baumannIn (G₁ ⊓ G₂) ≤ (pCore 2 G₁).map G₁.subtype ∨
      ¬ baumannIn (G₁ ⊓ G₂) ≤ (pCore 2 G₂).map G₂.subtype := by
  by_contra! hh
  have hn₁ := vertex_normalizes_baumann_of_le_core h hh.1
  have hn₂ : G₂ ≤ normalizer (baumannIn (G₁ ⊓ G₂) : Set G) := by
    simpa only [inf_comm G₂ G₁] using vertex_normalizes_baumann_of_le_core h.symm
      (by simpa only [inf_comm G₂ G₁] using hh.2)
  have he : baumannIn (G₁ ⊓ G₂) = ⊥ := h.common_normal_eq_bot hcore _ inf_le_left
    (normal_subgroupOf_of_le_normalizer hn₁) (normal_subgroupOf_of_le_normalizer hn₂)
  have hz : omegaOneCenter (G₁ ⊓ G₂) ≤ baumannIn (G₁ ⊓ G₂) := by
    intro z hz
    have hzT := (mem_omegaOneCenterAmbient_iff (G₁ ⊓ G₂) z).mp hz
    refine ⟨hzT.1, ?_⟩
    change z ∈ centralizer (omegaOneCenter (elementaryAbelianMaxJ (G₁ ⊓ G₂)) : Set G)
    intro x hx
    have hJT : elementaryAbelianMaxJ (G₁ ⊓ G₂) ≤ G₁ ⊓ G₂ := sSup_le fun _ hA => hA.1
    exact hzT.2.2 x ((map_subtype_le _).trans hJT hx)
  have hzb : omegaOneCenter (G₁ ⊓ G₂) = ⊥ := le_bot_iff.mp (hz.trans_eq he)
  rcases h.omega_center_moved hcore with hm | hm <;> simp [hzb] at hm

/-- The actual opposite-core noncontainment used to select the second local actor. -/
theorem IsGoldschmidtTriple.baumann_not_le_right_core_of_le_left
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hleft : baumannIn (G₁ ⊓ G₂) ≤ (pCore 2 G₁).map G₁.subtype) :
    ¬ baumannIn (G₁ ⊓ G₂) ≤ (pCore 2 G₂).map G₂.subtype :=
  (h.baumann_not_le_both_cores hcore).resolve_left (not_not.mpr hleft)

end CFSG.Quasithin.ChapterF
