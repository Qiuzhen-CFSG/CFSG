module
public import Theory.SpecificGroups.Alternating.SevenRankOneSection
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import Theory.GroupTheory.PerfectCenterFrattini
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Binary rank-one sections of perfect central covers of A₇

Project the actual perfect subgroup to A₇. A central supplement cannot
fill a perfect group, so properness survives. The restricted solvable
kernel preserves the simple intrinsic two-core quotient. The seven-point
coset argument then forces field order four, retaining the central cover.

Source application: Aschbacher–Smith A.3.12(6–7) and 5.2.2,
printed pp.47–48,648–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace alternatingGroup.SevenRankOneSection
variable {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]

/-- A proper perfect binary rank-one section in a perfect central A₇ cover has degree two. -/
theorem degree_eq_two_of_central_cover
    (e : (G ⧸ center G) ≃* alternatingGroup (Fin 7))
    (B : Subgroup G) [Group.IsPerfect B] (hp : B ≠ ⊤)
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (a : (B ⧸ pCore 2 B) ≃* PSL(2,F)) : n = 2 := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
    rw [hF]
    exact (show (4:ℕ) = 2^2 from rfl).le.trans (Nat.pow_le_pow_right (by decide) hn))
  let : IsSimpleGroup (B ⧸ pCore 2 B) := a.isSimpleGroup
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hk : q.ker = center G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hproper : B.map q ≠ ⊤ := by
    intro he
    apply hp
    apply eq_top_of_sup_center_eq_top
    have hh := congrArg (comap q) he
    simpa only [comap_map_eq,hk,comap_top] using hh
  let r := q.subgroupMap B
  let : Group.IsSolvable r.ker := by
    change Group.IsSolvable (q.subgroupMap B).ker
    rw [ker_subgroupMap,hk]
    exact Group.isSolvable_of_isSolvable_injective
      (f := B.subtype.subgroupComap (center G))
      (fun x y hh => Subtype.ext (Subtype.ext (congrArg (fun z : center G => (z : G)) hh)))
  let a' := (PerfectCoreTwoExtension.solvableKernelQuotientEquiv r
    (q.subgroupMap_surjective B)).symm.trans a
  exact degree_eq_two hF hn (B.map q) hproper (pCore 2 (B.map q))
    (a'.trans (Theory.PSL2.sl2QuotientEquiv F).symm)
end alternatingGroup.SevenRankOneSection
