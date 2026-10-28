module

public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSevenCoordinates
public import Theory.Representation.AlternatingSevenConjugatePair.Model.Natural
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSetup
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledFF

/-!
# The original doubled A₇ orbit and its ambient two-rank

The faithful seed marking identifies the component image with A₇. Its
center is trivial, so the action kernel in the original component is
characteristic. The original inverse-conjugation twist descends through
this kernel. Multiplication coordinates identify the actual orbit with
the seed action and that same descended twist, retaining the two original
conjugate seed subgroups. Their marked nonisomorphism survives descent.

The trivial commutant of this pair and relative normality embed the full
ambient automizer into its linear normalizer, proving two-rank at most
three. The global w and r bounds of 7.5.5 remain separate obligations.
The internal import reuses the characteristic-kernel and coordinate proofs
of the companion doubled FF module without changing their public boundary.
Source: Aschbacher--Smith D.3.10, H.8 and 7.5.5, printed pp.201,389,701.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Representation.AlternatingSevenConjugatePair.Model
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem seed_seven_marking [IsElementaryAbelian 2 V]
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (m : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ) :
    ∃ q : L →* alternatingGroup (Fin 7), Function.Surjective q ∧ q.ker.Characteristic ∧
      ∃ e : Additive V ≃ₗ[ZMod 2] Four,
        ∀ l v, e (doubledSeedAction L V D.normalizes l v) = σ (q l) (e v) := by
  let f := m.groupEquiv
  let q := f.toMonoidHom.comp D.componentHom
  have hq : Function.Surjective q := f.surjective.comp D.componentHom_surjective
  let : Nontrivial (alternatingGroup (Fin 7)) := f.symm.toEquiv.nontrivial
  let : q.ker.Characteristic := quotient_center_kernel D h f
    (alternatingGroup.center_eq_bot (by simp))
  let e := (seedCoordinates D).symm.trans m.linearEquiv
  have he : ∀ l v, e (doubledSeedAction L V D.normalizes l v) = σ (q l) (e v) := by
    intro l v
    obtain ⟨w,rfl⟩ := (seedCoordinates D).surjective v
    rw [← seedCoordinates_action D]
    simp only [e,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
    exact m.intertwines (D.componentHom l) w
  exact ⟨q,hq,inferInstance,e,he⟩

/-- The literal pair marking, retaining the original conjugator, its descended
automorphism, the characteristic kernel, and both original seed axes. -/
theorem sourceOrbit_seven_pair_coordinates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ)) :
    ∃ t : G, ∃ ht : t ∈ (T : Subgroup G), t ∉ normalizer (V : Set G) ∧
      ∃ q : L →* alternatingGroup (Fin 7), Function.Surjective q ∧ q.ker.Characteristic ∧
      ∃ a : MulAut (alternatingGroup (Fin 7)),
        (∀ l, a (q l) = q (doubledTwist L t (D.sylow_normalizes_component ht) l)) ∧
        (¬ Nonempty (σ.Equiv (σ.comp a.toMonoidHom))) ∧
        ∃ e : Additive D.sourceOrbit ≃ₗ[ZMod 2] (Four × Four),
          (∀ l v, e (doubledSeedAction L D.sourceOrbit
            D.sourceOrbit_component_normalizes l v) =
              (σ.prod (σ.comp a.toMonoidHom)) (q l) (e v)) ∧
          (∀ v, (e v).2 = 0 ↔ (v.toMul : G) ∈ V) ∧
          (∀ v, (e v).1 = 0 ↔ (v.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) := by
  let := D.elementary
  obtain ⟨q,hq,hker,e,he⟩ := seed_seven_marking D h σ hmodel.some
  let : q.ker.Characteristic := hker
  obtain ⟨t,ht,hnt,hne,c,hmul,hc⟩ := D.sourceOrbit_marked_doubled_coordinates hd
  let α := doubledTwist L t (D.sylow_normalizes_component ht)
  obtain ⟨a,ha⟩ := descend_twist q hq α
  have hneq : ¬ Nonempty (σ.Equiv (σ.comp a.toMonoidHom)) := by
    rintro ⟨b⟩
    let d := (e.trans b.toLinearEquiv).trans e.symm
    apply hne
    refine ⟨Representation.Equiv.mk d ?_⟩
    intro l
    apply LinearMap.ext
    intro v
    apply e.injective
    change e (d (doubledSeedAction L V D.normalizes l v)) =
      e (doubledSeedAction L V D.normalizes (α l) (d v))
    rw [he]
    change e (e.symm (b (e (doubledSeedAction L V D.normalizes l v)))) =
      σ (q (α l)) (e (e.symm (b (e v))))
    rw [e.apply_symm_apply,e.apply_symm_apply,he,← ha]
    exact LinearMap.congr_fun (b.isIntertwining' (q l)) (e v)
  let E := c.symm.trans (e.prodCongr e)
  refine ⟨t,ht,hnt,q,hq,hker,a,ha,hneq,E,?_,?_,?_⟩
  · intro l v
    obtain ⟨w,rfl⟩ := c.surjective v
    rw [← hc]
    simp only [E,LinearEquiv.trans_apply,c.symm_apply_apply]
    apply Prod.ext
    · exact he l w.1
    · change e (doubledSeedAction L V D.normalizes (α l) w.2) = σ (a (q l)) (e w.2)
      rw [he,ha]
  · intro v
    change e (c.symm v).2 = 0 ↔ (v.toMul : G) ∈ V
    rw [e.map_eq_zero_iff]
    have hc0 (w : Additive V) : ((c (w,0)).toMul : G) = (w.toMul : G) := by
      simpa using hmul w 0
    constructor
    · intro hz
      have hv : c ((c.symm v).1,0) = v := by rw [← hz]; exact c.apply_symm_apply v
      rw [← hv,hc0]
      exact (c.symm v).1.toMul.property
    · intro hv
      let w : Additive V := Additive.ofMul ⟨v.toMul,hv⟩
      have hw : c (w,0) = v := by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact hc0 w
      rw [← hw,c.symm_apply_apply]
  · intro v
    change e (c.symm v).1 = 0 ↔ _
    rw [e.map_eq_zero_iff]
    have hc0 (w : Additive V) : ((c (0,w)).toMul : G) = t * (w.toMul : G) * t⁻¹ := by
      simpa using hmul 0 w
    constructor
    · intro hz
      have hv : c (0,(c.symm v).2) = v := by rw [← hz]; exact c.apply_symm_apply v
      rw [← hv,hc0]
      exact mem_map_of_mem (MulAut.conj t).toMonoidHom (c.symm v).2.toMul.property
    · rintro ⟨w,hw,hv⟩
      let z : Additive V := Additive.ofMul ⟨w,hw⟩
      have hz : c (0,z) = v := by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact (hc0 z).trans hv
      rw [← hz,c.symm_apply_apply]

/-- The two-rank bound concerns the full automizer of the original orbit. -/
theorem sourceOrbit_seven_automizer_rank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ)) :
    primeRank 2 (ChapterE.Automizer D.sourceOrbit) ≤ 3 := by
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
  obtain ⟨_,_,_,q,hq,_,a,_,hne,e,he,_⟩ := D.sourceOrbit_seven_pair_coordinates h hd σ hmodel
  exact doubledSeven_rank_of_marked_normal_range σ (σ.comp a.toMonoidHom)
    hσ (hσ.comp a.injective) four_dimension hne
    (ChapterE.automizerRepresentation W) (ChapterE.automizerRepresentation_injective W)
    i q hq e he

/-- The original whole orbit, as opposed to either seed, has dimension eight. -/
theorem sourceOrbit_seven_dimension
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ)) :
    Module.finrank (ZMod 2) (Additive D.sourceOrbit) = 8 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,e,_⟩ := D.sourceOrbit_seven_pair_coordinates h hd σ hmodel
  exact e.finrank_eq.trans eight_dimension

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
