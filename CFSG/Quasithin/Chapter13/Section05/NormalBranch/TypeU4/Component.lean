module

public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.TypeU4.Geometry
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceComponent

/-!
# The component subgroup in the original Chapter13 branch

The actual returning plane supplies IsType, and its original cubic
component gives a nonsolvable subgroup of order3265920 containing the
full source involution centralizer. The point and line normalizers
generate this subgroup; its global equality with G is still to be proved.

Source: Aschbacher–Smith,13.5.16, pp.921–922; Asc94,45.10–45.11, pp.248–249.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.TypeU4
open Theory.GroupTheory.Recognition
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {M : Subgroup G} {g : G}

theorem cubic_component_subgroup_of_returning_plane
    (h : D.Hypothesis) (b : Conclusions D M 6 g) (hM : M = D.L)
    (z : G) (hz : z ∈ D.V₁) (hz1 : z ≠ 1)
    (V₂ : Subgroup G) (hline : D.V₁ ≤ V₂) (hseed : V₂ ≤ D.Vplus)
    (hfour : Nat.card V₂ = 4) (y : G)
    (hy : y ∈ normalizer (V₂ : Set G)) (hyH : y ∉ D.H)
    (hpair : D.UH ⊓ UnitaryFourThree.conjugate D.UH y = V₂)
    (P : Sylow 3 (UnitaryFourThree.centralizer z)) :
    ∃ ht : UnitaryFourThree.IsType z,
      ∃ c : UnitaryFourThree.CubicGeometry.SourceConfiguration ht P,
        Nat.card c.componentStabilizer = 3265920 ∧
        c.componentStabilizer = normalizer (c.W : Set G) ⊔ normalizer (c.V : Set G) ∧
        D.H ≤ c.componentStabilizer ∧ Odd c.componentStabilizer.index ∧
        ¬3 ∣ c.componentStabilizer.index ∧ ¬Group.IsSolvable c.componentStabilizer := by
  let ht := isType_of_returning_plane h b hM z hz hz1 V₂ hline hseed hfour y hy hyH hpair
  obtain ⟨c, hc, hgen, hC, hodd, hthree, hns⟩ := ht.original_cubic_component_subgroup P
  exact ⟨ht, c, hc, hgen, (centralizer_eq h b z hz hz1) ▸ hC, hodd, hthree, hns⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.TypeU4
