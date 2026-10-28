module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.MovedPrime.Inputs
public import CFSG.Quasithin.ChapterB.Section06To07.IntrinsicMinimalParabolic
public import Theory.GroupTheory.CComponent.RadicalFree
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore

/-!
# The whole-group row when the moved configuration is minimal parabolic

Restrict the original component and prescribed full Sylow to the top
subgroup carrier. Simplicity makes the component center and two-core
trivial, so its literal two-core quotient retains the given PSL₂ model.
Thus the singleton consisting of the whole group is a structural cover.

Source: Aschbacher--Smith E.2.2, printed pp.215--216, and 10.3.3, p.756.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem simple_component_center_eq_bot {K : Subgroup H}
    (hK : IsComponent H K) [IsSimpleGroup K] : center K = ⊥ := by
  let := hK.2
  obtain hb | ht := IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) inferInstance
  · exact hb
  · exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp ht)).elim

theorem prime_row_top_of_minimal (S : Sylow 2 H)
    (hmin : ChapterB.IsMinimalParabolicOver S ⊤)
    (K : Subgroup H) (hK : IsComponent H K) [IsSimpleGroup K]
    (hgen : K ⊔ (S : Subgroup H) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp7 : 7 ≤ p)
    (hm : ClassicalGroup.IsPSL K 2 p) : IsPrimeParabolicRow S ⊤ := by
  let L := K.subgroupOf (⊤ : Subgroup H)
  let e : L ≃* K := subgroupOfEquivOfLe (show K ≤ ⊤ from le_top)
  have hL : IsComponent (⊤ : Subgroup H) L := hK.subgroupOf le_top
  let : IsSimpleGroup L := e.isSimpleGroup
  let := hL.2
  have hc : pCore 2 L = ⊥ := le_bot_iff.mp
    ((IsQuasisimple.pCore_le_center 2).trans (simple_component_center_eq_bot hL).le)
  let eq : (L ⧸ pCore 2 L) ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  obtain ⟨M, hM, _⟩ := hmin.1.2
  have hmin' := (ChapterB.intrinsic_minimalParabolic S ⊤ M hmin hM.1 hM.2).1
  refine ⟨le_top, Or.inr ⟨hmin', L,
    isCComponent_of_isSimpleGroup_of_isPerfect hL.1,
    IsQuasisimple.of_mulEquiv eq.symm, ?_, p, hp, ho, hp7,
    hm.of_mulEquiv (eq.trans e)⟩⟩
  apply map_injective (⊤ : Subgroup H).subtype_injective
  change (K.subgroupOf ⊤ ⊔ (S : Subgroup H).subgroupOf ⊤).map _ = _
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_top, map_subgroupOf_eq_of_le le_top,
    ← MonoidHom.range_eq_map, range_subtype, hgen]

theorem prime_cover_of_minimal (S : Sylow 2 H)
    (hmin : ChapterB.IsMinimalParabolicOver S ⊤)
    (K : Subgroup H) (hK : IsComponent H K) [IsSimpleGroup K]
    (hgen : K ⊔ (S : Subgroup H) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hp7 : 7 ≤ p)
    (hm : ClassicalGroup.IsPSL K 2 p) : HasPrimeParabolicCover S := by
  refine ⟨{⊤}, ?_, by simp⟩
  intro P hP
  have he : P = ⊤ := Set.mem_singleton_iff.mp hP
  subst P
  exact prime_row_top_of_minimal S hmin K hK hgen hp ho hp7 hm

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.ModelGeneration.Cover
