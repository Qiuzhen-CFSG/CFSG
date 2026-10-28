module
public import CFSG.Quasithin.ChapterE.Section03.Parameters.SectionNormalizer
public import Theory.GroupTheory.ReducedNormal.Defs

/-!
# The faithful induced action of a reduced local module

For U normalized by H, the literal induced automizer is the image of H's
conjugation on U. Its kernel is C_H(U), so reducedness of U in H gives a
trivial two-core in this actual image. All maps retain the original ambient
subgroups. Source application: Aschbacher–Smith E.4.1 and 12.4.1, pp.241,812.
-/
@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G]

/-- Conjugation by the whole normalizing subgroup, onto its actual automizer. -/
def normalizedLocalAction (U H : Subgroup G) (hn : H ≤ normalizer (U : Set G)) :
    H →* inducedAutomizer U H :=
  (localNormalizerAction U H).comp
    (H.subtype.codRestrict (H ⊓ normalizer (U : Set G)) fun h => ⟨h.property,hn h.property⟩)

theorem normalizedLocalAction_surjective (U H : Subgroup G)
    (hn : H ≤ normalizer (U : Set G)) :
    Function.Surjective (normalizedLocalAction U H hn) := by
  intro a
  obtain ⟨n,rfl⟩ := localNormalizerAction_surjective U H a
  exact ⟨⟨n,n.property.1⟩,rfl⟩

theorem normalizedLocalAction_kernel (U H : Subgroup G)
    (hn : H ≤ normalizer (U : Set G)) (hUH : U ≤ H) :
    (normalizedLocalAction U H hn).ker = centralizer (U.subgroupOf H : Set H) := by
  ext h
  change localNormalizerAction U H ⟨h,h.property,hn h.property⟩ = 1 ↔ _
  rw [localNormalizerAction_eq_one_iff]
  constructor
  · intro hc u hu
    exact Subtype.ext (hc u hu)
  · intro hc u hu
    exact congrArg H.subtype (hc ⟨u,hUH hu⟩ hu)

/-- Reducedness transfers through the literal centralizer quotient. -/
theorem inducedAutomizer_pCore_eq_bot_of_reduced
    (U H : Subgroup G) (hn : H ≤ normalizer (U : Set G)) (hUH : U ≤ H)
    (hr : IsPReduced 2 (U.subgroupOf H)) : pCore 2 (inducedAutomizer U H) = ⊥ := by
  let := hr.normal
  let a := normalizedLocalAction U H hn
  let e := (QuotientGroup.quotientMulEquivOfEq
    (normalizedLocalAction_kernel U H hn hUH).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective a (normalizedLocalAction_surjective U H hn))
  rw [← pCore_map_iso 2 e,hr.quotient_pCore_eq_bot,Subgroup.map_bot]

/-- Solvability passes to the original action image. -/
theorem inducedAutomizer_isSolvable (U H : Subgroup G)
    (hn : H ≤ normalizer (U : Set G)) (hs : Group.IsSolvable H) :
    Group.IsSolvable (inducedAutomizer U H) := by
  let := hs
  exact Group.isSolvable_of_surjective (f := normalizedLocalAction U H hn)
    (normalizedLocalAction_surjective U H hn)
end CFSG.Quasithin.ChapterE
