module

public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.JankoTwo.FiveQuotients
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.QuotientFamily
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.IntrinsicStructure
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Overlap
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer

/-!
# E-generation by the concrete Hall--Janko parabolics

The first parabolics have their actual intrinsic two-core quotients A₅ and
S₅. Lifting the proved rank-two bounds across these two-cores gives their
E-generation. The second inner parabolic is solvable by its S₃ × C₃ quotient
and normal two-kernel; adjoining the fixed normalizing outer involution
preserves solvability. Hence the second parabolics satisfy E.1.13.

The explicit subgroups contain the same certified Sylow subgroup and their
checked join is the whole degree-100 J₂ carrier, respectively its permutation
extension. Restriction and E-member inheritance (E.1.8) then give generation
for the entire group, as in E.1.12. No unspecified local calculation or
E-generation premise remains.

Source: Aschbacher--Smith E.1.12--14, printed p.214, citing Aschbacher
(1982), Lemma 4.9; the concrete parabolics also occur in F.1.12(I)(10)--(11),
printed p.263. All subgroup and quotient identifications come from the
checked ATLAS degree-100 carrier, not an alternate J₂ model.
-/

public section
namespace CFSG.Quasithin.ChapterE.JankoTwo

open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.ExceptionalParabolics
open Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed

private theorem pair_generates {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (P Q : Subgroup G) (hTP : (T : Subgroup G) ≤ P)
    (hTQ : (T : Subgroup G) ≤ Q) (hPQ : P ⊔ Q = ⊤)
    (hP : IsEGenerated 2 P) (hQ : IsEGenerated 2 Q) : IsEGenerated 2 G := by
  apply IsEGeneratedAt.isEGenerated (T := T)
  intro Ω hΩ
  apply top_unique
  change ⊤ ≤ ChiefOrbit.generationTarget 2 T Ω
  rw [← hPQ]
  exact sup_le (ChiefOrbit.overgroup_le_generationTarget T P hTP hΩ hP)
    (ChiefOrbit.overgroup_le_generationTarget T Q hTQ hΩ hQ)

theorem first_isEGenerated : IsEGenerated 2 l₁ := by
  obtain ⟨e⟩ := FirstParabolic.l₁_quotient
  exact IsEGenerated.of_normal_two_subgroup (pCore 2 l₁) pCore_isPGroup
    (alternating_five_isEGenerated.map_equiv e.symm)

theorem outer_first_isEGenerated : IsEGenerated 2 l₁s := by
  obtain ⟨e⟩ := FirstParabolic.l₁s_quotient
  exact IsEGenerated.of_normal_two_subgroup (pCore 2 l₁s) pCore_isPGroup
    (symmetric_five_isEGenerated.map_equiv e.symm)

private theorem symmetric_three_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let N := alternatingGroup (Fin 3)
  let : IsCyclic N := isCyclic_of_prime_card (p := 3) (by
    change Nat.card (alternatingGroup (Fin 3)) = 3
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide)
  have hq : IsPGroup 2 (Equiv.Perm (Fin 3) ⧸ N) :=
    IsPGroup.of_card (n := 1) alternatingGroup.index_eq_two
  let : Group.IsNilpotent (Equiv.Perm (Fin 3) ⧸ N) := hq.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, inferInstance⟩

private theorem second_isSolvable : Group.IsSolvable p₂ := by
  let := symmetric_three_solvable
  obtain ⟨e⟩ := PairNormalizer.p₂_quotient_equiv
  let : Group.IsSolvable (p₂ ⧸ q₂.subgroupOf p₂) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hp : IsPGroup 2 (q₂.subgroupOf p₂) :=
    (IsPGroup.of_card (n := 6) PairNormalizer.card_q₂).comap_subtype
  let : Group.IsNilpotent (q₂.subgroupOf p₂) := hp.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (q₂.subgroupOf p₂)).mpr
    ⟨inferInstance, inferInstance⟩

private abbrev outerSecond : Subgroup Extension :=
  p₂.map intoExtension ⊔ Subgroup.zpowers outerElement

private theorem outer_second_isSolvable : Group.IsSolvable outerSecond := by
  let N := p₂.map intoExtension
  let C := Subgroup.zpowers outerElement
  let := second_isSolvable
  let : Group.IsSolvable N := Group.isSolvable_of_surjective
    (intoExtension.subgroupMap_surjective p₂)
  let : (N.subgroupOf outerSecond).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (sup_le N.le_normalizer
        (Subgroup.zpowers_le.mpr SecondParabolic.Overlap.outerElement_normalizes_p₂))
  let : Group.IsSolvable (N.subgroupOf outerSecond) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (show N ≤ outerSecond from le_sup_left)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (show N ≤ outerSecond from le_sup_left)).injective
  let : Group.IsSolvable (C.subgroupOf outerSecond) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (show C ≤ outerSecond from le_sup_right)).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (show C ≤ outerSecond from le_sup_right)).injective
  apply Group.isSolvable_of_normal_sup_eq_top (N.subgroupOf outerSecond)
    (C.subgroupOf outerSecond)
  rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
  exact Subgroup.subgroupOf_self _

theorem carrier_isEGenerated : IsEGenerated 2 Carrier := by
  let T := SecondParabolic.sylow FirstParabolic.card_l₁
  let := second_isSolvable
  exact pair_generates T l₁ p₂ SecondParabolic.s_le_l₁ PairNormalizer.s_le_p₂
    SecondParabolic.Overlap.l₁_sup_p₂ first_isEGenerated
    (isEGenerated_one_of_solvable.mono (by decide))

theorem extension_isEGenerated : IsEGenerated 2 Extension := by
  let T := SecondParabolic.outerSylow FirstParabolic.card_l₁
  let := outer_second_isSolvable
  apply pair_generates T l₁s outerSecond
    (show outerS ≤ l₁s from le_sup_right)
    (sup_le ((Subgroup.map_mono PairNormalizer.s_le_p₂).trans le_sup_left) le_sup_right)
    _ outer_first_isEGenerated (isEGenerated_one_of_solvable.mono (by decide))
  rw [FirstParabolic.l₁s_eq_sup_outerElement]
  change (l₁.map intoExtension ⊔ Subgroup.zpowers outerElement) ⊔
    (p₂.map intoExtension ⊔ Subgroup.zpowers outerElement) = ⊤
  rw [sup_sup_sup_comm, sup_idem, ← Subgroup.map_sup,
    SecondParabolic.Overlap.l₁_sup_p₂, ← MonoidHom.range_eq_map]
  exact SecondParabolic.Overlap.range_sup_outer FirstParabolic.card_l₁

end CFSG.Quasithin.ChapterE.JankoTwo
