module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import CFSG.Quasithin.ClassicalModels
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.FieldTheory.Finite.GaloisField
/-!
# The original A₈ section under solvable quotients

The specified PSL₄(2) quotient is identified with the actual A₈ carrier.
Its simple two-core quotient survives every solvable ambient kernel because
the smaller group is perfect. Local-component membership and the original
normalizer action survive the same map. The alternating containing rows
through degree eight and the binary degree-four row force equality by order.

Source: Aschbacher–Smith A.3.12 and15.3.32(3), printed pp.47–48 and1133.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
variable {G H : Type*} [Group G] [Group H]
noncomputable def modelEquiv (h : ClassicalGroup.IsPSL G 4 2) :
    G ≃* alternatingGroup (Fin 8) :=
  Classical.choice <| by
    obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
    let : Fintype F := Fintype.ofFinite F
    have hcard' : Fintype.card F = Fintype.card (ZMod 2) := by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard
    exact ⟨(e.trans (Atlas.fieldEquivPSL 4 (FiniteField.ringEquivOfCardEq hcard'))).trans
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8⟩
theorem model_card (h : ClassicalGroup.IsPSL G 4 2) : Nat.card G = 20160 := by
  rw [Nat.card_congr (modelEquiv h).toEquiv, nat_card_alternatingGroup]
  norm_num
theorem model_simple (h : ClassicalGroup.IsPSL G 4 2) : IsSimpleGroup G := by
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  exact (modelEquiv h).isSimpleGroup
variable [Finite G] [Finite H]
theorem section_map (B : Subgroup G) [Group.IsPerfect B]
    (hB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (f : G →* H) [Group.IsSolvable f.ker] :
    ClassicalGroup.IsPSL ((B.map f) ⧸ pCore 2 (B.map f)) 4 2 := by
  let : IsSimpleGroup (B ⧸ pCore 2 B) := model_simple hB
  let g := f.subgroupMap B
  let : Group.IsSolvable g.ker := by
    change Group.IsSolvable (f.subgroupMap B).ker
    rw [Subgroup.ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := B.subtype.subgroupComap f.ker) (fun a b he => Subtype.ext (Subtype.ext
        (congrArg (fun x : f.ker => (x : G)) he)))
  exact hB.of_mulEquiv
    (PerfectCoreTwoExtension.solvableKernelQuotientEquiv g (f.subgroupMap_surjective B)).symm

omit [Finite G] [Finite H] in
/-- Local C-components are perfect in their original carrier. -/
private theorem perfect_of_local {S B : Subgroup G} (hB : B ∈ localCComponents S) :
    Group.IsPerfect B := by
  let := hB.perfect
  let e := subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

/-- Literal local membership, normalization and the A₈ section survive a solvable kernel. -/
theorem local_section_map {S B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : S ≤ normalizer (B : Set G))
    (hsection : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (f : G →* H) [Group.IsSolvable f.ker] :
    B.map f ∈ localCComponents (S.map f) ∧
      S.map f ≤ normalizer (B.map f : Set H) ∧
      ClassicalGroup.IsPSL ((B.map f) ⧸ pCore 2 (B.map f)) 4 2 := by
  let := perfect_of_local hB
  exact ⟨Chapter1.Section02.localCComponents_map_of_solvable_ker hB f,
    (map_mono hSB).trans (le_normalizer_map f), section_map B hsection f⟩

omit [Finite H] in
/-- A containing group of order at most |A₈| is the actual smaller subgroup. -/
theorem eq_top_of_card_le (B : Subgroup G)
    (hsection : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (hG : Nat.card G ≤ 20160) : B = ⊤ := by
  have hB : 20160 ≤ Nat.card B := by
    rw [← model_card hsection]
    exact Nat.card_le_card_of_surjective (QuotientGroup.mk' (pCore 2 B))
      (QuotientGroup.mk'_surjective _)
  exact B.eq_top_of_card_eq (le_antisymm
    (Nat.card_le_card_of_injective B.subtype B.subtype_injective) (hG.trans hB))

omit [Finite H] in
/-- All alternating containing rows through A₈ force equality. -/
theorem eq_top_of_alternating (B : Subgroup G)
    (hsection : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    {n : ℕ} (hn : 5 ≤ n ∧ n ≤ 8) (e : G ≃* alternatingGroup (Fin n)) : B = ⊤ := by
  apply eq_top_of_card_le B hsection
  rw [Nat.card_congr e.toEquiv]
  obtain ⟨hn5, hn8⟩ := hn
  interval_cases n <;> rw [nat_card_alternatingGroup] <;> norm_num [Nat.factorial]

omit [Finite H] in
/-- The binary degree-four containing row forces equality. -/
theorem eq_top_of_binary_four (B : Subgroup G)
    (hsection : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    (hG : ClassicalGroup.IsPSL G 4 2) : B = ⊤ :=
  eq_top_of_card_le B hsection (model_card hG).le

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
