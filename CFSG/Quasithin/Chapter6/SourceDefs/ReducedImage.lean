module

public import CFSG.Quasithin.Chapter6.SourceDefs
public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.ElementaryAbelian.Injective

/-!
# The ambient and intrinsic reduced subgroup

The subgroup R₂(H) defined as an ambient join in the source configuration
is the image of the intrinsic reducedTwoSubgroup H. Restriction to H and
its inclusion identify the two families of reduced normal elementary
subgroups, including their literal centralizer quotients.

Source: Aschbacher–Smith, B.2.11–12, printed pp.77–78.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter6.Source
variable {G : Type*} [Group G]

theorem reducedSubgroup_eq_map (H : Subgroup G) :
    reducedSubgroup H = (Theory.GroupTheory.reducedTwoSubgroup H).map H.subtype := by
  apply le_antisymm
  · apply sSup_le
    rintro A ⟨hAH,hAE,hn,hq⟩
    let : IsElementaryAbelian 2 A := hAE
    have hA : Theory.GroupTheory.IsPReduced 2 (A.subgroupOf H) :=
      ⟨hn,IsElementaryAbelian.of_injective
        (subgroupOfEquivOfLe hAH).toMonoidHom (subgroupOfEquivOfLe hAH).injective,hq⟩
    have he := map_mono (f:=H.subtype) hA.le_reducedPSubgroup
    rwa [map_subgroupOf_eq_of_le hAH] at he
  · apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro A hA
    apply map_le_iff_le_comap.mp
    apply le_sSup
    have he : (A.map H.subtype).subgroupOf H = A :=
      comap_map_eq_self_of_injective H.subtype_injective _
    refine ⟨map_subtype_le _,?_,?_⟩
    · let := hA.elementary
      exact IsElementaryAbelian.map _
    · have hn : ((A.map H.subtype).subgroupOf H).Normal := he.symm ▸ hA.normal
      refine ⟨hn,?_⟩
      have transport : ∀ (B : Subgroup H) (hB : B.Normal), B=A →
          letI := hB
          pCore 2 (H ⧸ centralizer (B:Set H)) = ⊥ := by
        intro B hB hBA
        subst B
        exact hA.quotient_pCore_eq_bot
      exact transport _ hn he


end CFSG.Quasithin.Chapter6.Source
end
