module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.Geometry

/-!
# Normalization by the original odd prime actor

A three- or five-group has no nontrivial two-group quotient. Thus the
original prime actor lies in the two-residual of the literal Thompson
normalizer. The earlier residual-normalization conclusion then makes it
normalize the selected component. This uses relative subgroup inclusions,
without asserting that the component is normal in the ambient group.

Source: Aschbacher--Smith 15.1.19(7) and 15.1.21(ii), printed pp.1094,1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}

/-- Oddness of the source prime supplies two-perfection of the actual actor. -/
theorem RankOnePrimeActor.twoPerfect {d : CaseIComponentData T M Mc V}
    {Y : Subgroup G} (y : d.RankOnePrimeActor p Y) (hp : p = 3 ∨ p = 5) :
    IsPPerfect 2 Y := by
  have hc : Nat.Coprime p 2 := by rcases hp with rfl | rfl <;> decide
  intro N hN hquot
  let := hN
  have hd := IsPGroup.disjoint_of_coprime
    ((y.prime_group.to_quotient N).to_subgroup ⊤) (hquot.to_subgroup ⊤) hc
  apply top_unique
  intro a _
  apply (QuotientGroup.eq_one_iff a).mp
  exact Subgroup.disjoint_def.mp hd (mem_top _) (mem_top _)

/-- The odd prime actor is contained in the original Thompson residual. -/
theorem RankOnePrimeActor.le_thompsonResidual {d : CaseIComponentData T M Mc V}
    {Y : Subgroup G} (y : d.RankOnePrimeActor p Y) (hp : p = 3 ∨ p = 5) :
    Y ≤ d.rankOneThompsonResidual := by
  have he := subgroupOfEquivOfLe y.normalizer_le
  have hperfect : IsPPerfect 2 (Y.subgroupOf d.rankOneThompsonNormalizer) :=
    (y.twoPerfect hp).of_surjective he.symm.toMonoidHom he.symm.surjective
  have hh := map_mono (f := d.rankOneThompsonNormalizer.subtype)
    (le_pResidual_of_isPPerfect _ hperfect)
  simpa only [rankOneThompsonResidual, map_subgroupOf_eq_of_le y.normalizer_le] using hh

/-- The earlier residual theorem, rather than ambient normality, gives the action on L. -/
theorem PreExclusionSource.primeActor_normalizes
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p) {Y : Subgroup G}
    (y : d.RankOnePrimeActor p Y) (hp : p = 3 ∨ p = 5) :
    Y ≤ normalizer (d.L : Set G) :=
  (y.le_thompsonResidual hp).trans
    (d.rankOneThompsonResidual_le.trans (le_sup_left.trans s.residual_normalizes))

/-- The set-product identity SY=YS preserves the whole S-orbit L₀, even
when S does not normalize the selected component L. -/
theorem PreExclusionSource.primeActor_normalizes_orbit
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p) {Y : Subgroup G}
    (y : d.RankOnePrimeActor p Y) (hp : p = 3 ∨ p = 5) :
    Y ≤ normalizer (conjugateSpanBy d.L d.S : Set G) := by
  have hn := s.primeActor_normalizes (h := h) y hp
  apply le_normalizer_closure_iff.mpr
  rintro a ha x ⟨b, hb, l, hl, rfl⟩
  have hab : a * b ∈ (d.S : Set G) * (Y : Set G) := by
    rw [y.permutes]
    exact Set.mul_mem_mul ha hb
  obtain ⟨b', hb', a', ha', he⟩ := Set.mem_mul.mp hab
  refine subset_closure ⟨b', hb', a' * l * a'⁻¹,
    le_normalizer_iff.mp hn a' ha' l hl, ?_⟩
  calc
    b' * (a' * l * a'⁻¹) * b'⁻¹ = (b' * a') * l * (b' * a')⁻¹ := by group
    _ = (a * b) * l * (a * b)⁻¹ := by rw [he]
    _ = a * (b * l * b⁻¹) * a⁻¹ := by group

/-- The actor preserves the actual J(S), using the original equality J(S)=J(T). -/
theorem RankOnePrimeActor.normalizes_local_thompson
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    {Y : Subgroup G} (y : d.RankOnePrimeActor p Y)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    Y ≤ normalizer (elementaryAbelianMaxJ d.S : Set G) := by
  have he := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).1
  change elementaryAbelianMaxJ d.S = elementaryAbelianMaxJ (T : Subgroup G) at he
  rw [he]
  exact y.normalizer_le.trans inf_le_right

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
