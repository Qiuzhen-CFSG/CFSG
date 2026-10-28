module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSymplecticDerived
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.SymplecticTwo
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSetup
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledFF

/-!
# The actual A₆ doubled orbit and its full automizer

The polar equivalence identifies the deleted six-letter seed action with
Sp₄(2)′, retaining its genuine derived carrier. The centerless marking makes
the action kernel characteristic, so the actual inverse-conjugation twist
descends to that carrier. Its extension to full Sp₄(2) moves the diagram,
as otherwise the two original seeds would be isomorphic.

The resulting coordinates preserve both seed axes. Relative normality then
puts the entire ambient automizer in the paired normalizer, giving m ≥ 3
and the strict a < 2. The global weak-closure upper bound remains separate.
Source: Aschbacher--Smith H.7 and 7.3.2--7.3.5, printed pp.388--389,698--699.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem seed_six_marking [IsElementaryAbelian 2 V]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (m : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)) :
    ∃ q : L →* commutator (Sp (ZMod 2)), Function.Surjective q ∧ q.ker.Characteristic ∧
      ∃ e : Additive V ≃ₗ[ZMod 2] Vector (ZMod 2),
      ∀ l v, e (doubledSeedAction L V D.normalizes l v) =
        symplecticDerivedNatural 2 (q l) (e v) := by
  let d := ExtensionConsequences.SymplecticTwo.derivedNaturalActionEquiv
  let a := ExtensionConsequences.actionSymm d
  let f := m.groupEquiv.trans a.groupEquiv
  let q := f.toMonoidHom.comp D.componentHom
  have hq : Function.Surjective q := f.surjective.comp D.componentHom_surjective
  let : Nontrivial (commutator (Sp (ZMod 2))) := f.symm.toEquiv.nontrivial
  have hz : center (commutator (Sp (ZMod 2))) = ⊥ := by
    apply bot_unique
    intro z hz
    have hc : d.groupEquiv z ∈ center (alternatingGroup (Fin 6)) := by
      apply mem_center_iff.mpr
      intro g
      obtain ⟨x,rfl⟩ := d.groupEquiv.surjective g
      exact (map_mul d.groupEquiv x z).symm.trans
        ((congrArg d.groupEquiv (mem_center_iff.mp hz x)).trans (map_mul d.groupEquiv z x))
    rw [alternatingGroup.center_eq_bot (by norm_num), mem_bot] at hc
    exact mem_bot.mpr (d.groupEquiv.injective (hc.trans (map_one d.groupEquiv).symm))
  let : q.ker.Characteristic := quotient_center_kernel D h f hz
  let e := (seedCoordinates D).symm.trans (m.linearEquiv.trans a.linearEquiv)
  have he : ∀ l v, e (doubledSeedAction L V D.normalizes l v) =
      symplecticDerivedNatural 2 (q l) (e v) := by
    intro l v
    obtain ⟨w,rfl⟩ := (seedCoordinates D).surjective v
    rw [← seedCoordinates_action D]
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    exact (congrArg a.linearEquiv (m.intertwines (D.componentHom l) w)).trans
      (a.intertwines (m.groupEquiv (D.componentHom l)) (m.linearEquiv w))
  exact ⟨q,hq,inferInstance,e,he⟩

/-- The actual conjugator and its nonisomorphic seed twist give graph-pair
coordinates on the whole chosen orbit, retaining both original axes. -/
theorem sourceOrbit_six_pair_coordinates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ q : L →* commutator (Sp (ZMod 2)), Function.Surjective q ∧
      ∃ e : Additive D.sourceOrbit ≃ₗ[ZMod 2] Space (ZMod 2),
        (∀ l v, e (doubledSeedAction L D.sourceOrbit
          D.sourceOrbit_component_normalizes l v) = derivedPair graphAut (q l) (e v)) ∧
        (∀ v, (e v).2 = 0 ↔ (v.toMul : G) ∈ V) ∧
        (∀ v, (e v).1 = 0 ↔ (v.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) := by
  let := D.elementary
  have hmark := @seed_six_marking G _ _ T L V D D.elementary h hmodel.some
  let q := hmark.choose
  have hq : Function.Surjective q := hmark.choose_spec.1
  let : q.ker.Characteristic := hmark.choose_spec.2.1
  let e := hmark.choose_spec.2.2.choose
  have he := hmark.choose_spec.2.2.choose_spec
  have hcoords := @sourceOrbit_marked_doubled_coordinates G _ T L V D D.elementary hd
  let t := hcoords.choose
  have ht : t ∈ (T : Subgroup G) := hcoords.choose_spec.choose
  have hpair := hcoords.choose_spec.choose_spec
  have hne := hpair.2.1
  let c := hpair.2.2.choose
  have hc : ∀ l v, c (doubledPairAction L V D.normalizes t
      (D.sylow_normalizes_component ht) l v) = doubledSeedAction L D.sourceOrbit
      D.sourceOrbit_component_normalizes l (c v) := hpair.2.2.choose_spec.2
  have hmul : ∀ v w, ((c (v,w)).toMul : G) =
      (v.toMul : G) * (t * (w.toMul : G) * t⁻¹) := hpair.2.2.choose_spec.1
  let α := doubledTwist L t (D.sylow_normalizes_component ht)
  have haut := descend_twist q hq α
  obtain ⟨E,hE,hzero',hzero⟩ := doubledSymplectic_derived_pair_coordinates
    (doubledSeedAction L V D.normalizes) q e he α haut.choose haut.choose_spec hne
  let C := c.symm.trans E
  refine ⟨t,ht,hpair.1,q,hq,C,?_,?_,?_⟩
  · intro l v
    obtain ⟨w,rfl⟩ := c.surjective v
    rw [← hc]
    simp only [C, LinearEquiv.trans_apply, c.symm_apply_apply]
    exact hE l w
  · intro v
    change (E (c.symm v)).2 = 0 ↔ (v.toMul : G) ∈ V
    rw [hzero]
    have hc0 (w : Additive V) : ((c (w,0)).toMul : G) = (w.toMul : G) := by
      simpa using hmul w 0
    constructor
    · intro hz
      have hv : c ((c.symm v).1,0) = v := by
        rw [← hz]
        exact c.apply_symm_apply v
      rw [← hv, hc0]
      exact (c.symm v).1.toMul.property
    · intro hv
      let w : Additive V := Additive.ofMul ⟨v.toMul,hv⟩
      have hw : c (w,0) = v := by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact hc0 w
      rw [← hw, c.symm_apply_apply]
  · intro v
    change (E (c.symm v)).1 = 0 ↔ _
    rw [hzero']
    have hc0 (w : Additive V) : ((c (0,w)).toMul : G) =
        t * (w.toMul : G) * t⁻¹ := by
      simpa using hmul 0 w
    constructor
    · intro hz
      have hv : c (0,(c.symm v).2) = v := by
        rw [← hz]
        exact c.apply_symm_apply v
      rw [← hv, hc0]
      exact mem_map_of_mem (MulAut.conj t).toMonoidHom (c.symm v).2.toMul.property
    · rintro ⟨w,hw,hv⟩
      let z : Additive V := Additive.ofMul ⟨w,hw⟩
      have hz : c (0,z) = v := by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact (hc0 z).trans hv
      rw [← hz, c.symm_apply_apply]

/-- H.7's binary derived bounds on the full ambient automizer of the original orbit.
The global centralizer and weak-closure estimates remain separate obligations. -/
theorem sourceOrbit_six_local_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6))) :
    3 ≤ ChapterE.localM D.sourceOrbit ∧
      ChapterE.localA D.sourceOrbit < (2 : ℕ∞) := by
  let W := D.sourceOrbit
  let N := normalizer (W : Set G)
  let qN := W.normalizerMonoidHom.rangeRestrict
  let i : L →* ChapterE.Automizer W :=
    qN.comp (inclusion D.sourceOrbit_component_normalizes)
  have hi : i.range = (L.subgroupOf N).map qN := by
    ext a
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨inclusion D.sourceOrbit_component_normalizes l,l.property,rfl⟩
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,hl⟩,rfl⟩
  let : (L.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer
    (D.sourceOrbit_normalizer_le h.toHypothesis1221)
  let : i.range.Normal := hi ▸ Normal.map inferInstance qN
    W.normalizerMonoidHom.rangeRestrict_surjective
  obtain ⟨_,_,_,q,hq,E,hE,_⟩ := D.sourceOrbit_six_pair_coordinates h hd hmodel
  exact doubledSymplectic_parameters_of_marked_derived_range
    (ChapterE.automizerRepresentation W) (ChapterE.automizerRepresentation_injective W)
    i q hq E hE (n := 1) (by simp) (by decide)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
