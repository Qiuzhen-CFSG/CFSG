module
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalSimpleImage
public import CFSG.Quasithin.ChapterE.Section02.Structure.BinaryExclusions.Models
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalBender

/-!
# The actual normal-component source cases after binary exclusions

Apply the genuine Theorem C list to the literal image of the original
normal C-component in H/J. The original Sylow image remains minimal
parabolic there. The constructed invariant parabolics exclude every higher
binary family, preserving exactly the Bender, PSL₃ and Sp₄ rows and the
unresolved alternating, odd-characteristic and sporadic source cases.
For the Bender row the original maximal intersection is its actual Borel.

Source: Aschbacher–Smith E.2.2, printed pp.215–216. This is an intermediate
classification with the remaining source families explicitly retained;
it does not assert their exclusion or their final maximal-subgroup geometry.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Structure
universe u
variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

/-- The literal normal star component after all higher binary families are excluded. -/
theorem source_normal_component_cases
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (D : Type u) [Group D] [Finite D], ChapterA.Section02.TheoremC κ D)
    (hH : IsSQTK κ H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    let D := K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))
    (∃ n : ℕ, n ≤ 8 ∧ Nonempty (D ≃* alternatingGroup (Fin n))) ∨
    ChapterA.Section02.IsTheoremCOddModel D ∨
    ClassificationModels.IsBenderModel D ∨
    (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSL D 3 (2^f)) ∨
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp D 2 (2^f)) ∨
    Nonempty (D ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) ∨
    ChapterA.Section02.IsTheoremCSporadicModel D := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  let D := K.map q
  let hq := QuotientGroup.mk'_surjective J
  let S := T.mapSurjective hq
  have hmin : ChapterB.IsMinimalParabolicOver S ⊤ :=
    ChapterB.minimalParabolic_surjective_core T hP q hq (by rw [QuotientGroup.ker_mk'])
  have hKD := source_normal_simple_image T hP hs K hK hgen
  have hmodel := source_normal_simple_catalogue hA hC hH T hP hs K hK hgen
  have hDS : D ⊔ (S : Subgroup (H ⧸ J)) = ⊤ := hKD.2.2.2
  cases hmodel with
  | alternating n hn e => exact Or.inl ⟨n,hn,e⟩
  | odd h => exact Or.inr (Or.inl h)
  | bender h => exact Or.inr (Or.inr (Or.inl h))
  | rank_two f hm =>
    rcases BinaryExclusions.rank_two_survivors S D hDS hmin hm with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f,h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f,h⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.2)))))
  | linear_binary n hn hm => exact (BinaryExclusions.not_linear_binary S D hDS hmin hn hm).elim
  | sporadic h => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

/-- A Bender model of the original star component supplies the actual maximal Borel. -/
theorem source_original_star_bender (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ClassificationModels.IsBenderModel
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)))) :
    let J := ChapterB.minimalParabolicCore T hP
    let q := QuotientGroup.mk' J
    let D := K.map q
    let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
    ((ChapterB.minimalParabolicMax T hP).map q).subgroupOf D =
      normalizer ((S : Subgroup (H ⧸ J)).subgroupOf D : Set D) ∧
    (ChapterB.minimalParabolicMax T hP).map q =
      ChapterF.Source.borel D (S : Subgroup (H ⧸ J)) ⊔ (S : Subgroup (H ⧸ J)) ∧
    Group.IsSolvable ((ChapterB.minimalParabolicMax T hP).map q) := by
  let J := ChapterB.minimalParabolicCore T hP
  let q := QuotientGroup.mk' J
  have hq := QuotientGroup.mk'_surjective J
  have hk : q.ker ≤ J := by rw [QuotientGroup.ker_mk']
  have hmin := ChapterB.minimalParabolic_surjective_core T hP q hq hk
  have hKD := source_normal_simple_image T hP hs K hK hgen
  have hc := source_normal_bender_conclusions (T.mapSurjective hq) hmin (K.map q)
    hKD.2.2.2 hm
  rw [← ChapterB.minimalParabolicMax_map_core T hP q hq hk] at hc
  exact hc
end CFSG.Quasithin.ChapterE.Structure
