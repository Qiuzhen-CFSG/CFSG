module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalCentralizers
public import CFSG.Quasithin.ChapterB.Section05.OuterSixThreeShape

/-!
# Recovering the B.5.7 construction on specified outer factors

Normality of the original factors follows from their multiplication map and
outer generator. The A₆ factor is a component of three-rank at least two;
the C₃ factor is noncentral and lies in the three-core. It also rules out
the central-Fitting branch of the cover reduction. The genuine B.5.7
construction therefore supplies its marked six-point action and cubic plane.
Cardinality identifies that three-core with the specified second factor.

`recover` retains the local intertwiner, both ambient centralizers, the
symmetric supplement, and the valid odd fixed/moved complement. It preserves
the fixed line in the five-dimensional augmentation core. Extending these
local coordinates to the whole parity actor remains a separate construction.

The only earlier inputs are complete universal B.5.1 (producer
`qt-b05-quasisimple`), B.5.2 and B.5.5 (`qt-b05-quotient-components`), A.2.1
(`qt-a-02`), and all six rows of I.1.3 (`qt-i-01`, including
`qt-i01-lie-a2`). The numerical multiplier bound used by the cover producer
is deduced here from the full table. No B.5.6/B.5.7 input is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.1–7,
printed pp.99, 103–106; application to 13.6.13, printed p.929.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction ChapterB.SourceInduction.HighThreeRank
open ModuleCalculation ModuleCalculation.NaturalCentralizers
universe u v
variable {G : Type u} [Group G] (c : ChapterB.OuterSixThreeShape G)

private theorem factors_commute : c.first ≤ centralizer (c.second : Set G) := by
  intro a ha b hb
  let f := (c.first ⊔ c.second).subtype.comp c.product.toMonoidHom
  have h : Commute ((⟨a, ha⟩, 1) : c.first × c.second) (1, ⟨b, hb⟩) := by
    simp [Commute, SemiconjBy]
  have he := h.map f
  have h1 : f (⟨a, ha⟩, 1) = a := by simp [f, c.product_apply]
  have h2 : f (1, ⟨b, hb⟩) = b := by simp [f, c.product_apply]
  rw [h1, h2] at he
  exact he.eq.symm

private theorem outer_normalizes {H : Subgroup G} {t : G}
    (h : ∃ α : MulAut H, (∀ a : H, (α a : G) = t * (a : G) * t⁻¹) ∧
      α ∉ (MulAut.conj (G := H)).range) : t ∈ normalizer (H : Set G) := by
  obtain ⟨α, hα, _⟩ := h
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hα ⟨x, hx⟩]
    exact (α ⟨x, hx⟩).property
  · intro hx
    obtain ⟨a, ha⟩ := α.surjective ⟨t * x * t⁻¹, hx⟩
    have he := (hα a).symm.trans (congrArg Subtype.val ha)
    have : (a : G) = x := by
      exact mul_left_cancel (mul_right_cancel he)
    exact this ▸ a.property

theorem first_normal : c.first.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← c.generates]
  exact sup_le (sup_le c.first.le_normalizer
    ((le_centralizer_iff.mp (factors_commute c)).trans (Subgroup.centralizer_le_normalizer _)))
    (zpowers_le.mpr (outer_normalizes c.firstOuter))

theorem second_normal : c.second.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← c.generates]
  exact sup_le (sup_le ((factors_commute c).trans (Subgroup.centralizer_le_normalizer _))
    c.second.le_normalizer) (zpowers_le.mpr (outer_normalizes c.secondOuter))

theorem second_card : Nat.card c.second = 3 := by
  rw [Nat.card_congr c.secondEquiv.toEquiv]
  exact Nat.card_zmod 3

theorem second_noncentral : ¬ c.second ≤ center G := by
  intro hc
  obtain ⟨α, hα, ho⟩ := c.secondOuter
  apply ho
  refine ⟨1, ?_⟩
  ext a
  rw [hα]
  have h := (mem_center_iff.mp (hc a.property)) c.element
  simp only [MulAut.conj_apply, one_mul, inv_one, mul_one]
  rw [h, mul_inv_cancel_right]


theorem second_le_threeCore : c.second ≤ pCore 3 G := by
  let := second_normal c
  exact le_sSup ⟨inferInstance, IsPGroup.of_card (n := 1) (by simpa using second_card c)⟩

theorem first_component : IsComponent G c.first := by
  let := first_normal c
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    simple := by
      exact ((QuotientGroup.quotientMulEquivOfEq
        (alternatingGroup.center_eq_bot (by simp))).trans
          QuotientGroup.quotientBot).isSimpleGroup }
  exact ⟨(inferInstance : c.first.Normal).isSubnormal, IsQuasisimple.of_mulEquiv c.firstEquiv.symm⟩

theorem first_rank [Finite G] : 1 < primeRank 3 c.first := by
  rw [primeRank_equiv 3 c.firstEquiv]
  exact lt_of_lt_of_le (by decide : 1 < 2)
    (alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide))

private theorem first_centerless (a : c.first) (ha : a ∈ center c.first) : a = 1 := by
  have h := (centerCongr c.firstEquiv ⟨a, ha⟩).property
  change c.firstEquiv a ∈ center (alternatingGroup (Fin 6)) at h
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at h
  exact c.firstEquiv.injective (h.trans c.firstEquiv.map_one.symm)

variable [Finite G]

theorem fitting_not_central : generalizedFitting G ≠ c.first ⊔ center G := by
  intro he
  apply second_noncentral c
  have hle := (second_le_threeCore c).trans
    ((pCore_le_fitting G 3).trans (fitting_le_generalizedFitting G))
  rw [he] at hle
  intro x hx
  obtain ⟨l, hl, z, hz, rfl⟩ := mem_sup_of_normal_right.mp (hle hx)
  have hxC : l * z ∈ centralizer (c.first : Set G) :=
    (le_centralizer_iff.mp (factors_commute c)) hx
  have hzC : z ∈ centralizer (c.first : Set G) := (center_le_centralizer _) hz
  have hlC : l ∈ centralizer (c.first : Set G) := by
    simpa using (centralizer (c.first : Set G)).mul_mem hxC
      ((centralizer (c.first : Set G)).inv_mem hzC)
  have hl1 : (⟨l, hl⟩ : c.first) = 1 := first_centerless c _ (by
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    exact hlC a a.property)
  have hl' : l = 1 := congrArg Subtype.val hl1
  simpa [hl'] using hz

open CoverCentralizer.SourceConstruction
open NaturalReduction.ModelComparison.BinaryG2Exclusion

/-- Only the complete universal earlier-source implications consumed by B.5.7. -/
structure EarlierSources (K : GroupClass.{u}) : Prop where
  cover : CoverInput K
  components : ComponentsInput.{u,v} K
  semisimple : SemisimpleInput K
  multipliers : EarlierMultiplierInput K
  quasisimple : ProjectiveLine.QuasisimpleClassificationInput.{u,v} K

private theorem multiplier_bound {K : GroupClass.{u}}
    (h : EarlierMultiplierInput K) : MultiplierInput K := by
  intro S _ _ _ _ hs
  rcases subsingleton_or_nontrivial (PerfectCentralCovering.schurMultiplier S) with ht | ht
  · let := ht
    rw [Nat.card_eq_one_iff_unique.mpr ⟨ht, inferInstance⟩]
    exact one_dvd _
  · let := ht
    obtain ⟨r, hr⟩ := (h S hs).exhaustive.mp ht
    obtain ⟨e⟩ := (h S hs).values r hr
    rw [Nat.card_congr e.toEquiv]
    cases r <;> norm_num [MultiplierShape.Carrier, Nat.card_prod, Nat.card_zmod]

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) G V) {K : GroupClass.{u}}

/-- The genuine source construction, still with its actual cover. -/
theorem noncentral_context (earlier : EarlierSources.{u,v} K)
    (hyp : FFHypothesis K ρ) : Nonempty (NoncentralContext K G c.first) := by
  rcases CoverCentralizer.reduction earlier.cover earlier.components earlier.semisimple
    (multiplier_bound earlier.multipliers) hyp (first_component c) (first_rank c) with h | h
  · exact (fitting_not_central c h.2).elim
  · exact h

/-- The marked local action and the original cubic plane, recovered from
B.5.7. The first component and second factor are the literal input subgroups. -/
structure Recovered where
  offender : Subgroup G
  best : IsBestOffender ρ offender
  model : SymmetricMovedModel ρ c.first offender
  marking :
    Nonempty (QuasisimpleSource.MarkedActionEquiv model.sectionData.space.toRepresentation ⊤
      (c.first.subgroupOf (c.first ⊔ offender))
      (BinaryPermutation.naturalRepresentation (Fin 6)) (alternatingGroup (Fin 6))) ∨
    Nonempty (QuasisimpleSource.MarkedActionEquiv model.sectionData.space.toRepresentation ⊤
      (c.first.subgroupOf (c.first ⊔ offender))
      (BinaryPermutation.coreRepresentation (Fin 6)) (alternatingGroup (Fin 6)))
  second_eq : c.second = pCore 3 G
  plane : Module.finrank (ZMod 2) (moved ρ c.second) = 2
  component_centralizer : centralizer (c.first : Set G) = c.second
  cubic_centralizer : centralizer (c.second : Set G) = c.first ⊔ c.second
  rank_eq : rank offender = 3
  component_fixedCodim_eq :
    fixedCodim model.sectionData.space.toRepresentation
      (offender.subgroupOf (c.first ⊔ offender)) = 2
  first_fixed : moved ρ c.first ≤ fixedSpace ρ c.second
  second_fixed : moved ρ c.second ≤ fixedSpace ρ c.first
  moved_product : moved ρ (c.first ⊔ c.second) = moved ρ c.first ⊔ moved ρ c.second
  disjoint : Disjoint (moved ρ c.first) (moved ρ c.second)
  cubic_complement : IsCompl (moved ρ c.second) (fixedSpace ρ c.second)
  supplement : (c.first ⊔ offender) ⊔ c.second = ⊤
  supplement_disjoint : Disjoint (c.first ⊔ offender) c.second
  component_index : c.first.relIndex (c.first ⊔ offender) = 2

/-- B.5.7 recovers the local six-point action, cubic plane and the valid
supplement/decomposition clauses from complete earlier inputs. -/
theorem recover (earlier : EarlierSources.{u,v} K) (hyp : FFHypothesis K ρ) :
    Nonempty (Recovered c ρ) := by
  obtain ⟨d⟩ := noncentral_context c ρ earlier hyp
  let : c.first.Normal := d.normal
  have hL := first_component c
  obtain ⟨A, hA, hm, _, _⟩ := exists_moving_offender ρ hyp hL d
  obtain ⟨m⟩ := NaturalReduction.model_of_earlier_source ρ earlier.quasisimple
    earlier.multipliers hyp hL (first_rank c) d hA hm
  have hf := threeCore_fixes_model ρ ConcreteModels.modelCommutants hL d m
  let e := source_offender_plane ρ hyp hL d hA hm hf m
  obtain ⟨cc⟩ := cubicCentralizers_of_offender_conclusion ρ hyp hL d m e
  have hX : c.second = pCore 3 G := eq_of_le_of_card_ge (second_le_threeCore c) (by
    rw [second_card c, Nat.card_congr cc.threeCoreEquiv.toEquiv]
    exact le_of_eq (Nat.card_zmod 3))
  have hdec := threeCore_moved_decomposition ρ hL d hf
  have hs : (c.first ⊔ A) ⊔ c.second = ⊤ ∧
      Disjoint (c.first ⊔ A) c.second ∧ c.first.relIndex (c.first ⊔ A) = 2 := by
    rw [hX, ← cc.component_centralizer]
    rcases e.marking with hn | hc
    · obtain ⟨b⟩ := hn
      exact marked_symmetric_supplement ρ m
        (BinaryPermutation.naturalRepresentation (Fin 6))
        CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.symmetricAction_injective
        CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.normalizer_alternatingImage b
    · obtain ⟨b⟩ := hc
      exact marked_symmetric_supplement ρ m
        (BinaryPermutation.coreRepresentation (Fin 6))
        CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.coreAction_injective
        ConcreteModels.core_six_normalizer b
  refine ⟨{
    offender := A
    best := hA
    model := m
    marking := e.marking
    second_eq := hX
    plane := by rw [hX]; exact e.plane
    component_centralizer := cc.component_centralizer.trans hX.symm
    cubic_centralizer := by rw [hX]; exact cc.threeCore_centralizer
    rank_eq := e.rank_eq
    component_fixedCodim_eq := e.component_fixedCodim_eq
    first_fixed := by rw [hX]; exact hf
    second_fixed := by rw [hX]; exact hdec.2.2
    moved_product := by rw [hX]; exact hdec.1
    disjoint := by rw [hX]; exact hdec.2.1
    cubic_complement := odd_moved_complement ρ c.second (by rw [second_card c]; decide)
    supplement := hs.1
    supplement_disjoint := hs.2.1
    component_index := hs.2.2 }⟩


end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Exceptional.SourceAction
