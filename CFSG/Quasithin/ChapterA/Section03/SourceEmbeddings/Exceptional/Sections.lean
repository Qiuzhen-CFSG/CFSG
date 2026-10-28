module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ThreeRank
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison
public import Theory.AtlasPort.Janko2.Sporadic.Janko2
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.Mathieu.M22.Properties.ThreeRank
public import Theory.Mathieu.M23.Properties.Simplicity
public import Theory.Mathieu.M23.Properties.Order
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.SpecificGroups.PSL3Four.ThreeRank
public import Theory.Quasithin.CoprimeRank
/-!
# The exceptional sections in the component embedding argument

The three actual carriers J₂, M₂₃ and PSL₃(4) are simple, have three-rank
at least two, and have order divisible by 20160. Their identifications
survive a solvable ambient kernel when the smaller group is perfect.
The transport retains the original local component and its Sylow actor.

These are the section invariants used to inspect the containing component
in the exceptional application of A.3.12. PSL₃(4) is retained as its actual
matrix carrier, independently of the different group PSL₄(2) of equal order.
Source: Aschbacher–Smith A.3.12, printed pp.47–48, and 13.6.27, p.934.
-/
@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional

/-- The actual exceptional simple carriers used by the local seed. -/
def IsModel (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Sporadic.LeechRelated.J2.Carrier) ∨
  Nonempty (X ≃* Sporadic.Mathieu.M23) ∨
  Nonempty (X ≃* Matrix.PSL3Four.PSL)

variable {X Y : Type*} [Group X] [Group Y]

theorem IsModel.of_equiv (h : IsModel Y) (e : X ≃* Y) : IsModel X := by
  rcases h with h | h | h
  all_goals obtain ⟨j⟩ := h
  · exact Or.inl ⟨e.trans j⟩
  · exact Or.inr (Or.inl ⟨e.trans j⟩)
  · exact Or.inr (Or.inr ⟨e.trans j⟩)

theorem IsModel.isSimple (h : IsModel X) : IsSimpleGroup X := by
  rcases h with h | h | h
  all_goals obtain ⟨e⟩ := h
  · let := Atlas.Sporadic.Janko2.isSimpleGroup
    let : IsSimpleGroup Sporadic.LeechRelated.J2.Carrier :=
      Sporadic.LeechRelated.J2.IcosianComparison.comparison.isSimpleGroup
    exact e.isSimpleGroup
  · let := Sporadic.Mathieu.m23_isSimpleGroup
    exact e.isSimpleGroup
  · let : IsSimpleGroup Matrix.PSL3Four.PSL := Atlas.psl_simple_high_rank 3 (by decide)
    exact e.isSimpleGroup

theorem IsModel.card (h : IsModel X) :
    Nat.card X = 604800 ∨ Nat.card X = 10200960 ∨ Nat.card X = 20160 := by
  rcases h with h | h | h
  all_goals obtain ⟨e⟩ := h
  · exact .inl ((Nat.card_congr e.toEquiv).trans
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier)
  · exact .inr (.inl ((Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m23_order))
  · exact .inr (.inr ((Nat.card_congr e.toEquiv).trans Matrix.PSL3Four.card_PSL))

theorem IsModel.card_dvd (h : IsModel X) : 20160 ∣ Nat.card X := by
  rcases h.card with he | he | he <;> rw [he] <;> norm_num

theorem IsModel.threeRank [Finite X] (h : IsModel X) : 2 ≤ primeRank 3 X := by
  rcases h with h | h | h
  all_goals obtain ⟨e⟩ := h
  · rw [primeRank_congr 3 e]
    exact Sporadic.LeechRelated.J2.three_rank_ge_two
  · rw [primeRank_congr 3 e]
    have he := primeRank_congr 3 Sporadic.Mathieu.m23EquivM22PointStabilizer
    rw [Sporadic.Mathieu.m22_primeRank_three] at he
    exact he.le.trans (primeRank_subgroup_le 3 _)
  · rw [primeRank_congr 3 e]
    exact Matrix.PSL3Four.ThreeRank.three_rank_ge_two

variable {G H : Type*} [Group G] [Group H]

theorem section_card_dvd {B : Subgroup G} (h : IsModel (B ⧸ pCore 2 B)) :
    20160 ∣ Nat.card B := h.card_dvd.trans (card_quotient_dvd_card _)

theorem ambient_card_dvd {B : Subgroup G} (h : IsModel (B ⧸ pCore 2 B)) :
    20160 ∣ Nat.card G := (section_card_dvd h).trans B.card_subgroup_dvd_card

/-- Perfection is intrinsic to the original smaller group. -/
theorem local_perfect {S B : Subgroup G} (hB : B ∈ localCComponents S) :
    Group.IsPerfect B := by
  let := hB.perfect
  let e := subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

variable [Finite G] [Finite H]

omit [Finite H] in
theorem section_threeRank {B : Subgroup G} (h : IsModel (B ⧸ pCore 2 B)) :
    2 ≤ primeRank 3 B := by
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 B) pCore_isPGroup]
  exact h.threeRank

/-- The exceptional two-core quotient survives a solvable ambient kernel. -/
theorem section_map (B : Subgroup G) [Group.IsPerfect B]
    (h : IsModel (B ⧸ pCore 2 B)) (f : G →* H) [Group.IsSolvable f.ker] :
    IsModel ((B.map f) ⧸ pCore 2 (B.map f)) := by
  let : IsSimpleGroup (B ⧸ pCore 2 B) := h.isSimple
  let g := f.subgroupMap B
  let : Group.IsSolvable g.ker := by
    change Group.IsSolvable (f.subgroupMap B).ker
    rw [Subgroup.ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := B.subtype.subgroupComap f.ker) (fun a b he => Subtype.ext (Subtype.ext
        (congrArg (fun x : f.ker => (x : G)) he)))
  exact h.of_equiv
    (PerfectCoreTwoExtension.solvableKernelQuotientEquiv g (f.subgroupMap_surjective B)).symm

/-- Local membership, the original Sylow normalization, and the same
exceptional carrier survive the literal solvable quotient map. -/
theorem local_section_map {S B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : S ≤ normalizer (B : Set G)) (h : IsModel (B ⧸ pCore 2 B))
    (f : G →* H) [Group.IsSolvable f.ker] :
    B.map f ∈ localCComponents (S.map f) ∧
      S.map f ≤ normalizer (B.map f : Set H) ∧
      IsModel ((B.map f) ⧸ pCore 2 (B.map f)) := by
  let := local_perfect hB
  exact ⟨Chapter1.Section02.localCComponents_map_of_solvable_ker hB f,
    (map_mono hSB).trans (le_normalizer_map f), section_map B h f⟩

omit [Finite H] in
theorem eq_top_of_card_le (B : Subgroup G) (h : IsModel (B ⧸ pCore 2 B))
    (hG : Nat.card G ≤ 20160) : B = ⊤ := by
  have hB : 20160 ≤ Nat.card B :=
    Nat.le_of_dvd (Nat.card_pos (α := B)) (section_card_dvd h)
  exact B.eq_top_of_card_eq (le_antisymm
    (Nat.card_le_card_of_injective B.subtype B.subtype_injective) (hG.trans hB))

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
