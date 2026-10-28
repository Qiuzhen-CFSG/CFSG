module
public import CFSG.Quasithin.ChapterF.Section01.RankOneMathieuLocal
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Rank-one local components in a central triple cover of M₂₂

The cover order still divides the M₂₄ order, so a nonsolvable source rank-one
section is PSL₂(4) or PSL₂(8). Its simple quotient and perfectness make the
restricted central kernel a two-group. The actual central projection therefore
preserves its intrinsic two-core quotient and its full normalizing Sylow.
The proved M₂₂ local theorem excludes the field-eight alternative.

Source: Aschbacher–Smith A.3.12–14 and 5.2.2, pp.47–49,648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.MathieuLocal
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G]

/-- The full central triple cover retains the actual right two-core quotient:
a normalized source rank-one local component has quotient PSL₂(4). -/
theorem rankOne_quotient_four_of_central_cover
    (e : (G ⧸ center G) ≃* M22) (hc : Nat.card (center G) = 3)
    (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hm : IsRankOneModel (B ⧸ pCore 2 B)) :
    ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4 := by
  have hd : Nat.card G ∣ 244823040 := by
    rw [card_eq_card_quotient_mul_card_subgroup (center G),
      Nat.card_congr e.toEquiv,m22_order,hc]
    decide
  have hns : ¬ Group.IsSolvable (B ⧸ pCore 2 B) := by
    intro hs
    let := hs
    let : Group.IsNilpotent (pCore 2 B) := pCore_isNilpotent
    let : Group.IsSolvable B := Group.isSolvable_of_ker_le_range (pCore 2 B).subtype
      (QuotientGroup.mk' (pCore 2 B)) (by simp)
    exact hl.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup G) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).injective)
  apply (hm.mathieu_section hns ((card_quotient_dvd_card _).trans
    (B.card_subgroup_dvd_card.trans hd))).resolve_right
  intro h8
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := h8
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := a.isSimpleGroup
  let : Group.IsPerfect B := FiveLocalFF.SolvableQuotients.local_perfect hl
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = center G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let : Group.IsSolvable q.ker := hk ▸ inferInstance
  let r := q.subgroupMap B
  let : Group.IsSolvable r.ker := by
    change Group.IsSolvable (q.subgroupMap B).ker
    rw [ker_subgroupMap,hk]
    exact Group.isSolvable_of_isSolvable_injective
      (f := B.subtype.subgroupComap (center G))
      (fun x y hh => Subtype.ext (Subtype.ext (congrArg (fun z : center G => (z : G)) hh)))
  let b := PerfectCoreTwoExtension.solvableKernelQuotientEquiv r (q.subgroupMap_surjective B)
  exact not_eight_m22 (S.mapSurjective hq) (B.map q)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl q)
    ((map_mono hn).trans (le_normalizer_map q))
    ⟨F,inferInstance,inferInstance,hF,⟨b.symm.trans a⟩⟩

end CFSG.Quasithin.ChapterF.Source.MathieuLocal
