module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SmallSourceClassification
public import Theory.GroupAction.CentralKernelFixedComponents
public import Theory.GroupAction.PerfectCentralQuotient
/-!
# The original fixed component survives the containing central quotient

The original source theorem makes K simple. Its actual fixed-component copy
therefore has trivial center and injects through the containing central quotient.
The fixed-subgroup image is normal in the full quotient fixed subgroup, so the
image remains an ordinary component there. Perfectness makes the induced
quotient automorphism faithful, retaining order two and the literal quotient map.

Source: Aschbacher–Smith 2.5.19, p.561, where the containing central quotient
is inspected before the remaining cover and fusion arguments.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection

/-- The original source K and involution survive the literal central quotient. -/
theorem source_fixed_component_central_quotient {G:Type*} [Group G] [Finite G]
    {H K M:Subgroup G} {S:Sylow 2 H} {z:G}
    (c:MathieuSourceSetup H K M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=K⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel K)
    {E:Type*} [Group E] [Group.IsPerfect E]
    (a:MulAut E) (ha:orderOf a=2)
    (B:Subgroup a.fixedSubgroup) (hB:IsComponent a.fixedSubgroup B) (eK:K≃*B) :
    let b:=quotientAut (center E) a
    let q:=QuotientGroup.mk' (center E)
    ∃hcompat:∀x:E,q (a x)=b (q x),
      orderOf b=2 ∧
      IsComponent b.fixedSubgroup (B.map (MulAut.fixedSubgroupMap a b q hcompat)) ∧
      Nonempty (K≃*B.map (MulAut.fixedSubgroupMap a b q hcompat)) := by
  let b:=quotientAut (center E) a
  let q:=QuotientGroup.mk' (center E)
  have hcompat:∀x:E,q (a x)=b (q x):=fun x=>(quotientAut_apply_mk (center E) a x).symm
  have hb2:orderOf b=2:=
    (orderOf_injective (quotientAut (center E)) MulAut.quotient_center_injective a).trans ha
  let : IsSimpleGroup K:=(ComponentSelection.MathieuSourceSetup.small_source_structure c hG hempty hgen hb).2.1
  let : IsSimpleGroup B:=eK.symm.isSimpleGroup
  let : IsQuasisimple B:=hB.2
  have hZ:center B=⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center B) inferInstance with h|h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp h)).elim
  obtain ⟨hD,⟨e⟩⟩:=MulAut.fixedSubgroupMap_component_of_center_eq_bot a b q
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hcompat B hB hZ
  exact ⟨hcompat,hb2,hD,⟨eK.trans e⟩⟩
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
