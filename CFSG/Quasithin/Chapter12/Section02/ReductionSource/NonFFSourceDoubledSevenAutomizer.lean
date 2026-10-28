module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSevenCoordinates
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSevenAutomizer

/-!
# S₇ is the actual ambient automizer of the doubled A₇ orbit

The faithful seven-letter embedding agrees with the original component
quotient. If the seed-moving element of T had even image, surjectivity of
that quotient would identify its orbit action with an element of L. Their
quotient would centralize the whole orbit and hence normalize the seed,
contrary to the original marking. Thus the ambient image contains both
A₇ and an odd permutation, and is all of S₇.

The resulting coordinates retain the same component map, conjugator,
inverse-conjugation twist and original seed axes. No ambient action or
group-family identification is assumed. The remaining local-centralizer
and global-parameter arguments of 7.5.5 are not asserted here.
Source: Aschbacher--Smith D.3.10, H.8 and 7.5.5, printed pp.201,389,701.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource ChapterB.QuasisimpleSource
open Representation.AlternatingSevenConjugatePair.Model
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Coordinates and compatible maps for the original doubled A₇ orbit.
Every field is constructed from the original marking below. -/
structure SevenActionCoordinates
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four) where
  conjugator : G
  in_sylow : conjugator ∈ (T : Subgroup G)
  moves_seed : conjugator ∉ normalizer (V : Set G)
  component : L →* alternatingGroup (Fin 7)
  component_surjective : Function.Surjective component
  component_kernel_characteristic : component.ker.Characteristic
  twist : MulAut (alternatingGroup (Fin 7))
  twist_compat : ∀ l, twist (component l) = component
    (doubledTwist L conjugator (D.sylow_normalizes_component in_sylow) l)
  inequivalent : ¬ Nonempty (σ.Equiv (σ.comp twist.toMonoidHom))
  coordinates : Additive D.sourceOrbit ≃ₗ[ZMod 2] (Four × Four)
  action : ∀ l v, coordinates (doubledSeedAction L D.sourceOrbit
    D.sourceOrbit_component_normalizes l v) =
      (σ.prod (σ.comp twist.toMonoidHom)) (component l) (coordinates v)
  first_axis : ∀ v, (coordinates v).2 = 0 ↔ (v.toMul : G) ∈ V
  second_axis : ∀ v, (coordinates v).1 = 0 ↔
    (v.toMul : G) ∈ V.map (MulAut.conj conjugator).toMonoidHom
  automizer : ChapterE.Automizer D.sourceOrbit ≃* Equiv.Perm (Fin 7)
  component_formula : ∀ l : L, automizer
    (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
      (inclusion D.sourceOrbit_component_normalizes l)) = (component l).val
  conjugator_odd : automizer (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
    ⟨conjugator,D.sourceOrbit_weakClosure_setup.normalizes in_sylow⟩) ∉ alternatingGroup (Fin 7)

/-- The original marked doubled seed constructs the full compatible S₇ action. -/
theorem sourceOrbit_seven_action_coordinates
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ)) :
    Nonempty (D.SevenActionCoordinates σ) := by
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
  obtain ⟨t,ht,hnt,q,hq,hker,a,ha,hne,e,he,hfirst,hsecond⟩ :=
    D.sourceOrbit_seven_pair_coordinates h hd σ hmodel
  obtain ⟨p,hp,hpi⟩ := doubledSeven_embedding_of_marked_normal_range
    σ (σ.comp a.toMonoidHom) hσ (hσ.comp a.injective) four_dimension hne
    (ChapterE.automizerRepresentation W) (ChapterE.automizerRepresentation_injective W)
    i q hq e he
  let tn : N := ⟨t,D.sourceOrbit_weakClosure_setup.normalizes ht⟩
  let z := qN tn
  have hz : p z ∉ alternatingGroup (Fin 7) := by
    intro hz
    obtain ⟨l,hl⟩ := hq ⟨p z,hz⟩
    have hil : i l = z := hp ((hpi l).trans (congrArg Subtype.val hl))
    let n : N := tn * (inclusion D.sourceOrbit_component_normalizes l)⁻¹
    have hn : qN n = 1 := by
      change qN (tn * (inclusion D.sourceOrbit_component_normalizes l)⁻¹) = 1
      rw [map_mul,map_inv,show qN (inclusion D.sourceOrbit_component_normalizes l) = z from hil]
      exact mul_inv_cancel z
    have hnc : n ∈ W.normalizerMonoidHom.ker := by
      exact congrArg (fun x : ChapterE.Automizer W => (x : MulAut W)) hn
    rw [Subgroup.normalizerMonoidHom_ker] at hnc
    have hVW : V ≤ W := by
      change V ≤ D.sourceOrbit
      rw [D.sourceOrbit_eq]
      exact le_componentOrbit V T
    have hc : (n : G) ∈ normalizer (V : Set G) :=
      (Subgroup.centralizer_le hVW).trans (Subgroup.centralizer_le_normalizer _) hnc
    have hlN : (l : G) ∈ normalizer (V : Set G) := D.normalizes l.property
    have hh := (normalizer (V : Set G)).mul_mem hc hlN
    apply hnt
    simpa only [n,coe_mul,coe_inv,coe_inclusion,tn,inv_mul_cancel_right] using hh
  have hps : Function.Surjective p := by
    have hA : alternatingGroup (Fin 7) ≤ p.range := by
      intro g hg
      obtain ⟨l,hl⟩ := hq ⟨g,hg⟩
      exact ⟨i l,(hpi l).trans (congrArg Subtype.val hl)⟩
    intro g
    change g ∈ p.range
    by_cases hg : g ∈ alternatingGroup (Fin 7)
    · exact hA hg
    have hs : g.sign = -1 := (Int.units_eq_one_or g.sign).resolve_left hg
    have hzs : (p z).sign = -1 := (Int.units_eq_one_or (p z).sign).resolve_left hz
    have hgz : g * (p z)⁻¹ ∈ alternatingGroup (Fin 7) := by
      rw [Equiv.Perm.mem_alternatingGroup,map_mul,map_inv,hs,hzs]
      decide
    have hh := p.range.mul_mem (hA hgz) (show p z ∈ p.range from ⟨z,rfl⟩)
    simpa only [inv_mul_cancel_right] using hh
  exact ⟨{
    conjugator := t
    in_sylow := ht
    moves_seed := hnt
    component := q
    component_surjective := hq
    component_kernel_characteristic := hker
    twist := a
    twist_compat := ha
    inequivalent := hne
    coordinates := e
    action := he
    first_axis := hfirst
    second_axis := hsecond
    automizer := MulEquiv.ofBijective p ⟨hp,hps⟩
    component_formula := hpi
    conjugator_odd := hz }⟩

/-- The ambient automizer attains the rank-three bound. -/
theorem sourceOrbit_seven_automizer_rank_eq
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) Four)
    (hσ : Function.Injective σ)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ)) :
    primeRank 2 (ChapterE.Automizer D.sourceOrbit) = 3 := by
  obtain ⟨C⟩ := D.sourceOrbit_seven_action_coordinates h hd σ hσ hmodel
  exact (primeRank_equiv 2 C.automizer).trans
    Representation.AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_symmetric

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
