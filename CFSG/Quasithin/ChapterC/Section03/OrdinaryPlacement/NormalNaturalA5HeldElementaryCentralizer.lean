module

public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryNormalizer
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryFixedData
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks.NodeMembers
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.WordCoverage

/-!
# Pure sixteen-subgroups recover the marked Held local overgroup

The exact listed elements of each order-64 row contain at most ten elements
outside class 2A fixing any vertex outside the row's fixed sextet. A pure
subgroup of order sixteen therefore has precisely that sextet as fixed points.
Its full normalizer preserves the sextet and lies in the already identified
literal local overgroup. This directly supplies the original ordinary placement
argument, without requiring a separate computation of its centralizer.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.OrdinaryPlacement.HeldElementaryCentralizer
open Held Held.LocalPairs.PairCoverage
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel
open Held.LocalPairs.SylowGeometry.Calculations
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue.RankSixCertificate
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration
open Held.TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks

private theorem entry_card (j : Fin 22) :
    Nat.card (entry j) = (members (some j)).toFinset.card := by
  classical
  have hinj : Function.Injective normalForm := by
    apply (normalForm_surjective.bijective_of_nat_card_le ?_).1
    simpa only [Nat.card_fin] using
      InnerNormalizer.representative_card_ge_of_orbit_labels
        InnerNormalizer.orbitSizeLabel_eq_card_orbit
  let f : (members (some j)).toFinset → entry j := fun m =>
    ⟨normalForm m, (certified_members (some j) _).mpr
      ⟨m, List.mem_toFinset.mp m.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b h
      exact Subtype.ext (hinj (congrArg Subtype.val h))
    · intro x
      obtain ⟨m, hm, he⟩ := (certified_members (some j) x).mp x.property
      exact ⟨⟨m, List.mem_toFinset.mpr hm⟩, Subtype.ext he⟩
  rw [← Nat.card_eq_finsetCard]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

private theorem row_card (k : Fin 2) : Nat.card (ambient (row k)) = 64 := by
  rw [ambient,card_map_of_injective representative.subtype_injective,entry_card]
  fin_cases k <;> decide +kernel

/-- Cardinality of the actual marked ambient elementary core. -/
theorem card_ambientWordCore (i : Bool) : Nat.card (ambientWordCore i) = 64 := by
  have hh (k : Fin 2) : Nat.card (ambientWordCore (k == 0)) = 64 := by
    have hc := row_card k
    rw [ambient_eq_conjugated_pCore,card_map_of_injective (MulAut.conj _).injective] at hc
    rw [ambientWordCore,wordCore_eq_pCore]
    fin_cases k <;> exact hc
  cases i
  · exact hh 1
  · exact hh 0

private def eligible (k : Fin 2) (x : Fin 2058) : Finset (Fin 1024) :=
  ((members (some (row k))).filter (fun n =>
    !Held.OrdinaryElementary.classA n && decide (normalFormAction n x = x))).toFinset

private theorem eligible_card (k : Fin 2) : ∀ x : Fin 2058,
    x ∉ sextet k → (eligible k x).card ≤ 10 :=
  FixedData.pure_members_fixing_card_le k

private theorem fixedPoints_pure_row (k : Fin 2) (E : Subgroup He)
    (hE : Nat.card E = 16) (hpure : ∀ x : E, ¬ IsConj Held.a (x : He))
    (hEi : E ≤ ambient (row k)) :
    MulAction.fixedPoints E (Fin 2058) = (sextet k : Set (Fin 2058)) := by
  classical
  ext x
  constructor
  · intro hx
    by_contra hn
    have hi (z : E) : ∃ n ∈ eligible k x, (normalForm n).val = z.val := by
      obtain ⟨y,hy,he⟩ := hEi z.property
      obtain ⟨n,hn,heq⟩ := (certified_members (some (row k)) y).mp hy
      have hz : (normalForm n).val = z.val := (congrArg Subtype.val heq).trans he
      refine ⟨n,?_,hz⟩
      apply List.mem_toFinset.mpr
      apply List.mem_filter.mpr
      refine ⟨hn,?_⟩
      have ha : Held.OrdinaryElementary.classA n = false := by
        apply Bool.eq_false_iff.mpr
        intro hh
        exact hpure z (hz ▸ (Held.OrdinaryElementary.classA_iff n).mp hh)
      simp only [ha,Bool.not_false,Bool.true_and,decide_eq_true_eq]
      rw [normalFormAction_eq,hz]
      exact hx z
    choose f hf he using hi
    have hc : Nat.card E ≤ Nat.card (eligible k x) := by
      apply Nat.card_le_card_of_injective (fun z => (⟨f z,hf z⟩ : eligible k x))
      intro z w hh
      apply Subtype.ext
      exact (he z).symm.trans ((congrArg (fun n => (normalForm n).val)
        (congrArg Subtype.val hh)).trans (he w))
    rw [hE,Nat.card_eq_finsetCard] at hc
    have hu := eligible_card k x hn
    omega
  · intro hx z
    have hh : x ∈ MulAction.fixedPoints (ambient (row k)) (Fin 2058) := by
      rw [fixedPoints_eq]
      exact hx
    exact hh ⟨z.val,hEi z.property⟩

private theorem normalizer_preserves_fixed {G X : Type*} [Group G] [MulAction G X]
    (E : Subgroup G) (g : G) (hg : g ∈ normalizer (E : Set G))
    (x : X) (hx : x ∈ MulAction.fixedPoints E X) :
    g • x ∈ MulAction.fixedPoints E X := by
  intro p
  have hp : g⁻¹ * p.val * g ∈ E := by
    simpa using (mem_normalizer_iff.mp ((normalizer (E : Set G)).inv_mem hg) p.val).mp
      p.property
  have he := hx (⟨g⁻¹ * p.val * g,hp⟩ : E)
  change (g⁻¹ * p.val * g) • x = x at he
  change p.val • (g • x) = g • x
  simpa only [mul_smul,smul_inv_smul] using congrArg (g • ·) he

private theorem normalizer_pure_row (k : Fin 2) (E : Subgroup He)
    (hE : Nat.card E = 16) (hpure : ∀ x : E, ¬ IsConj Held.a (x : He))
    (hEi : E ≤ ambient (row k)) : normalizer (E : Set He) ≤ candidateGroup k := by
  rw [← sextetStabilizer_eq_candidateGroup representative_isPGroup
    Held.Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup]
  intro g hg
  apply MulAction.mem_stabilizer_set.mpr
  intro x
  rw [← fixedPoints_pure_row k E hE hpure hEi]
  constructor
  · intro hx
    simpa only [inv_smul_smul] using
      normalizer_preserves_fixed E g⁻¹ (inv_mem hg) (g • x) hx
  · exact normalizer_preserves_fixed E g hg x

/-- Every pure subgroup of order sixteen in a marked elementary core has its
full ambient normalizer in that literal local overgroup. -/
theorem normalizer_pure_sixteen_le_local (E : Subgroup He)
    (hE : Nat.card E = 16) (hpure : ∀ x : E, ¬ IsConj Held.a (x : He))
    (i : Bool) (hEi : E ≤ ambientWordCore i) :
    normalizer (E : Set He) ≤ localOvergroup i := by
  have hh (k : Fin 2) (hEk : E ≤ ambientWordCore (k == 0)) :
      normalizer (E : Set He) ≤ localOvergroup (k == 0) := by
    let e := MulAut.conj (conjugator (index k))
    let F := E.map e.toMonoidHom
    have hF : Nat.card F = 16 := (card_map_of_injective e.injective).trans hE
    have hpF : ∀ x : F, ¬ IsConj Held.a (x : He) := by
      rintro ⟨x,hx⟩ hh
      obtain ⟨y,hy,rfl⟩ := hx
      exact hpure ⟨y,hy⟩ (hh.trans (isConj_iff.mpr ⟨(conjugator (index k))⁻¹,
        by simp [e,MulAut.conj_apply,mul_assoc]⟩))
    have hc : (ambientWordCore (k == 0)).map e.toMonoidHom = ambient (row k) := by
      rw [ambient_eq_conjugated_pCore,ambientWordCore,wordCore_eq_pCore]
      fin_cases k <;> rfl
    have hFC : F ≤ ambient (row k) := hc ▸ map_mono hEk
    have hn := normalizer_pure_row k F hF hpF hFC
    have hm : (normalizer (E : Set He)).map e.toMonoidHom ≤
        (localOvergroup (k == 0)).map e.toMonoidHom := by
      rw [map_normalizer_eq_of_bijective _ e.bijective]
      convert hn using 1; fin_cases k <;> rfl
    exact (map_le_map_iff_of_injective e.injective).mp hm
  cases i
  · exact hh 1 hEi
  · exact hh 0 hEi

end CFSG.Quasithin.ChapterC.OrdinaryPlacement.HeldElementaryCentralizer
