module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.FullSource
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.Quotient
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.MovedEndpoint
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.Actors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.FinalAssembly


/-!
# The selected exceptional critical pair on the genuine source action

The full marked tensor coordinates are on W = [U,K*], with U literally
U_H/V₁. Their ambient displacement bound excludes transvections on U.
We construct the conjugation section on that same carrier and identify its
action with the quotient action used by the critical geometry.

Relative component normality, two-perfectness and the intrinsic quasisimple
two-core quotient transport along each actual endpoint conjugator. Thus the
proved selection and component-generation argument in `FinalAssembly` gives
one critical pair with strict denominators, its quadratic member of Q,
every-F endpoint generation and rank(Vγ*) > 1. Double commutators prove
quadraticity of this same Vγ* on U. The actual H-conjugator supplies alpha,
its vertex and its subgroup, with Vα* ≤ O₂(L₁*T*).

The remaining source local calculation is O₂(L₁*T*) = T* ∩ K*. This module
does not assume or prove that identity, and does not assert the completed
exceptional endpoint. `EarlierInputs` lists only the authorized earlier
F.9 and §13.5/13.7 geometry; the full source setup is retained through
`F918Hypotheses`. No faithfulness on W or equality W = U is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.8.4(6), 13.8.8(2), 13.8.18(4), and the exceptional branch of 13.8.20(a),
printed pp.947, 949, 953–954; F.9.11–16, pp.321–324. Conjugation follows
the existing left-action convention; the source right conjugator is its inverse.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.CriticalInputs
open CriticalGeometry CriticalGeometry.SectionActions
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {G : Type*} [Group G] [Finite G]

/-- Construct the central-section realization on the literal source carrier. -/
noncomputable def sourceSection (H V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (hρ : SeedAction.IsConjugation H V₃ V₁ ρ)
    (hV₃H : V₃ ≤ H) (hV₁ : V₁ ≤ V₃)
    (hz : H ≤ centralizer (V₁ : Set G)) :
    ConjugationSection H (Source.UH H V₃) V₁ ρ where
  le := conjugateSpanBy_le_self hV₃H
  normalizes := le_normalizer_conjugateSpanBy V₃ H
  centralizes := hz
  line_le := hV₁.trans (le_conjugateSpanBy V₃ H)
  quotient := (MulEquiv.multiplicativeAdditive (Source.Utilde H V₃ V₁)).symm.toMonoidHom.comp
    (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)))
  surjective := (MulEquiv.multiplicativeAdditive (Source.Utilde H V₃ V₁)).symm.surjective.comp
    (QuotientGroup.mk'_surjective _)
  kernel := by ext x; exact QuotientGroup.eq_one_iff x
  conjugates := hρ

omit [Finite G] in
/-- The linearized quotient action is the given genuine source action. -/
theorem source_action_eq (H V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (hρ : SeedAction.IsConjugation H V₃ V₁ ρ)
    (hz : H ≤ normalizer (V₁ : Set G))
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁) (g : Source.Hstar H) :
    (binaryLinear (uStarAction H V₃ V₁ hz hQ g)).toLinearMap = ρ g := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
  ext v
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
  have hv : v = SeedAction.vector H V₃ V₁ u := congrArg Additive.ofMul hu.symm
  rw [hv, hρ, uStarAction_mk]
  exact congrArg Additive.ofMul (quotientAction_apply H (Source.UH H V₃) V₁ _ hz h u)

/-- Excluding rank-one displacements excludes nonidentity transvections in
the quotient-action convention used by the critical geometry. -/
theorem no_source_transvection (H V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (hρ : SeedAction.IsConjugation H V₃ V₁ ρ)
    (hz : H ≤ normalizer (V₁ : Set G))
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁)
    (hno : ∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1) :
    ∀ g, uStarAction H V₃ V₁ hz hQ g ≠ 1 →
      binaryLinear (uStarAction H V₃ V₁ hz hQ g) ∉
        LinearEquiv.transvections (ZMod 2) (SeedAction.Space H V₃ V₁) := by
  intro g hn ht
  have hr := LinearEquiv.mem_dilatransvections_iff_finrank.mp
    (LinearEquiv.transvections_subset_dilatransvections ht)
  rw [source_action_eq H V₃ V₁ ρ hρ hz hQ g] at hr
  have hzrank : Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) = 0 := by
    have := hno g
    omega
  have hzero : ρ g - LinearMap.id = 0 := by
    apply LinearMap.range_eq_bot.mp
    exact Submodule.finrank_eq_zero.mp hzrank
  have he : ρ g = LinearMap.id := sub_eq_zero.mp hzero
  apply hn
  ext w
  have hh := LinearMap.congr_fun (source_action_eq H V₃ V₁ ρ hρ hz hQ g) (Additive.ofMul w)
  rw [he] at hh
  exact hh

omit [Finite G] in
/-- Relative normality transports to the actual endpoint overgroup. -/
theorem endpoint_normal {L T H V : Subgroup G} (d : CriticalPair L T H V)
    (K : Subgroup G) (hKH : K ≤ H) [(K.subgroupOf H).Normal] :
    ((K.map (MulAut.conj (d.gb : G)).toMonoidHom).subgroupOf
      (vertexGroup L T H d.gamma)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  rw [d.vertexGroup_gamma]
  exact (map_mono (le_normalizer_of_normal_subgroupOf hKH)).trans
    (K.le_normalizer_map (MulAut.conj (d.gb : G)).toMonoidHom)

omit [Finite G] in
/-- Two-perfectness transports with the same endpoint conjugator. -/
theorem endpoint_residual {L T H V : Subgroup G} (d : CriticalPair L T H V)
    (K : Subgroup G) (hKH : K ≤ H) (hp : IsPPerfect 2 K) :
    pResidual 2 ((K.map (MulAut.conj (d.gb : G)).toMonoidHom).subgroupOf
      (vertexGroup L T H d.gamma)) = ⊤ := by
  have hle : K.map (MulAut.conj (d.gb : G)).toMonoidHom ≤ vertexGroup L T H d.gamma := by
    rw [d.vertexGroup_gamma]
    exact map_mono hKH
  let e := ((MulAut.conj (d.gb : G)).subgroupMap K).trans
    (subgroupOfEquivOfLe hle).symm
  exact (pResidual_eq_top_iff 2 _).mpr (hp.of_surjective e.toMonoidHom e.surjective)

/-- The intrinsic two-core quotient is conjugated before taking its actual
star image. No quotient kernel is discarded. -/
theorem endpoint_quasisimple {L T H V : Subgroup G} (d : CriticalPair L T H V)
    (K : Subgroup G) (hKH : K ≤ H) [(K.subgroupOf H).Normal]
    [IsQuasisimple (K ⧸ pCore 2 K)] :
    IsQuasisimple (Source.starImage (vertexGroup L T H d.gamma)
      (K.map (MulAut.conj (d.gb : G)).toMonoidHom)) := by
  have hle : K.map (MulAut.conj (d.gb : G)).toMonoidHom ≤ vertexGroup L T H d.gamma := by
    rw [d.vertexGroup_gamma]
    exact map_mono hKH
  let e := (MulAut.conj (d.gb : G)).subgroupMap K
  let eQ := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  exact IsQuasisimple.of_mulEquiv (eQ.trans (Structure.quotientStarEquiv _ _ hle
    ((endpoint_normal d K hKH).isSubnormal)))

/-- A finite C-component is two-perfect, also on its ambient carrier. -/
theorem component_twoPerfect (H K : Subgroup G) (hKH : K ≤ H)
    (hcomp : (K.subgroupOf H).IsCComponent) : IsPPerfect 2 K := by
  let : Group.IsPerfect (K.subgroupOf H) := hcomp.perfect
  have hp : IsPPerfect 2 (K.subgroupOf H) := by
    intro N hN hp
    let := hN
    have hsub : Subsingleton ((K.subgroupOf H) ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent
    apply eq_top_iff.mpr
    intro g _
    exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)
  exact hp.of_surjective (subgroupOfEquivOfLe hKH).toMonoidHom
    (subgroupOfEquivOfLe hKH).surjective

open CriticalGeometry.Reorientation
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData

/-- The precise earlier geometric inputs still discharged by the chapter owner.
`geometry` is F.9.11/13/15; the two edge-core bounds are F.9.13(1–2).
The line centralizer and noncentral section are the earlier §13.5/13.7
conclusions, and `estimate` is the factor-two bound of F.9.16(2).
There is no selected rank, quadratic action, conjugating element, or
placement in the component among these hypotheses. -/
structure EarlierInputs (L T H V V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁)) : Prop where
  geometry : ∀ d : CriticalPair L T H V, EarlierGeometry d V₃ V₁
  terminal_core : ∀ d : CriticalPair L T H V,
    Source.UH H V₃ ≤ (edgeGroup L T H d.gamma d.previous).pCoreIn 2
  centralizer : ⁅Source.VH H V, Source.HC H V₃⁆ ≤ V₁
  failure : ∀ d : CriticalPair L T H V, ¬ ⁅d.Ugamma V₃, V⁆ ≤ d.Aone V₁
  noncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃
  flag_index : V₃.relIndex V = 2
  edge_normalizes : (L ⊔ T) ⊓ H ≤ normalizer (V : Set G)
  endpoint_core : ∀ d : CriticalPair L T H V,
    d.Qgamma ≤ edgeGroup L T H d.gamma d.previous
  proper_edge : ∀ d : CriticalPair L T H V,
    edgeGroup L T H d.gamma d.previous < vertexGroup L T H d.gamma
  estimate : ∀ d : CriticalPair L T H V,
    0 < rank (Source.starImage H (d.Ugamma V₃)) →
    denominatorRank V₃ V₁ d ≤ rank (Source.starImage H (d.Ugamma V₃)) →
    fixedCodim ρ (Source.starImage H (d.Ugamma V₃)) ≤
      2 * rank (Source.starImage H (d.Ugamma V₃))
  initial_core : ∀ d : CriticalPair L T H V,
    d.Vgamma ≤ (edgeGroup L T H (base L T H true) d.second).pCoreIn 2

/-- One selected source pair, its actual H-conjugator, and the consequences
needed at the exceptional endpoint. The component placement remains a
separate local Borel calculation. -/
structure SelectedWitness (L T H V L₁ V₃ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁)) where
  pair : CriticalPair L T H V
  conjugator : H
  second_to_base : inG0 (L := L) (T := T) conjugator • pair.second = base L T H false
  actor_le : pair.Vgamma ≤ H
  strict_base : Source.DH (Source.UH H V₃) (pair.Ugamma V₃) (pair.Aone V₁) < Source.UH H V₃
  strict_endpoint : Source.Dgamma (pair.Ugamma V₃) (Source.UH H V₃) V₁ < pair.Ugamma V₃
  positive : 0 < rank (Source.starImage H (pair.Ugamma V₃))
  comparison : denominatorRank V₃ V₁ pair ≤ rank (Source.starImage H (pair.Ugamma V₃))
  quadratic_member : QuadraticMember ρ (Source.starImage H (pair.Ugamma V₃))
  generation : ∀ F : Subgroup G, F ≤ Source.UH H V₃ →
    ¬ F ≤ Source.DH (Source.UH H V₃) (pair.Ugamma V₃) (pair.Aone V₁) →
    vertexGroup L T H pair.gamma = conjugateSpanBy F (vertexGroup L T H pair.gamma) ⊔
      edgeGroup L T H pair.gamma pair.previous
  rank_gt_one : 1 < rank (Source.starImage H pair.Vgamma)
  quadratic : IsQuadratic ρ (Source.starImage H pair.Vgamma)
  conjugate_le_core : pair.Vgamma.map (MulAut.conj (conjugator : G)).toMonoidHom ≤
    (L₁ ⊔ T).pCoreIn 2

section SourceSelection
variable (H K L L₁ T V V₃ V₁ : Subgroup G)
    [(K.subgroupOf H).Normal]
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (P : Sylow 2 (Source.Hstar H)) {𝒦 : GroupClass}
    (f : FFSections.SourceOrbit.F918Hypotheses H K L L₁ T V V₃ V₁ ρ P 𝒦)

include f in
/-- Construct the strict critical pair and its genuine rank conclusion from
moved coordinates, without identifying W with the ambient source module. The ambient elementary-abelian instances are the earlier
F.9.11(2–3) conclusions for the source spans. -/
theorem exists_selected_witness
    (initial : CriticalPair L T H V) (hVH : V ≤ H)
    (e : EarlierInputs L T H V V₃ V₁ ρ)
    (s : Equiv.Perm (Fin 3) →* Source.Hstar H) (W : Subrepresentation ρ)
    (_hW : W.toSubmodule = subspaceCommutator ρ ⊤ (Source.starImage H K))
    (c : FFSections.LinearTwo.FiveReconstruction.FullCoordinates W.toRepresentation
      (Source.starImage H K) s) :
    Nonempty (SelectedWitness L T H V L₁ V₃ V₁ ρ) := by
  let q := sourceSection H V₃ V₁ ρ f.conjugation (f.setup.seed_le.trans hVH)
    f.setup.line_lt.le f.setup.fixes_line
  have hgen : H = K ⊔ (L₁ ⊔ T) := by
    rw [f.generation, f.single_component, f.overlap]
  have hz := f.setup.fixes_line.trans (Subgroup.centralizer_le_normalizer _)
  have hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁ := by
    rw [← f.kernel, commutator_comm]
    exact commutator_commutatorPreimage_le H (Source.UH H V₃) V₁ hz
  let : IsQuasisimple (K ⧸ pCore 2 K) := f.quasisimple_quotient
  have hp := component_twoPerfect H K f.component_le f.component
  obtain ⟨d, hd, hdγ, hpos, hcomp, hquad, ⟨h, hh, hplace, _⟩, hgenerate, hrank⟩ :=
    CriticalGeometry.CriticalPair.exists_selected_component_rank initial L₁ ((L₁ ⊔ T).pCoreIn 2)
      K V₃ V₁ q f.faithful hgen f.overlap
      (fun d => endpoint_normal d K f.component_le)
      (fun d => endpoint_residual d K f.component_le hp)
      (fun d => endpoint_quasisimple d K f.component_le)
      e.terminal_core f.setup.seed_le hVH hQ e.geometry f.setup.line_order
      e.centralizer e.failure e.noncentral e.flag_index e.edge_normalizes
      e.endpoint_core e.proper_edge e.estimate e.initial_core le_rfl
      (no_source_transvection H V₃ V₁ ρ f.conjugation hz hQ (c.no_transvection_on_ambient W))
  exact ⟨{
    pair := d
    conjugator := h
    second_to_base := hh
    actor_le := (e.geometry d).Vgamma_H
    strict_base := hd
    strict_endpoint := hdγ
    positive := hpos
    comparison := hcomp
    quadratic_member := hquad
    generation := hgenerate
    rank_gt_one := hrank
    quadratic := (d.quadratic_star_on_Utilde V₃ V₁ q f.setup.seed_le (e.geometry d).VH_endpoint).1
    conjugate_le_core := hplace }⟩

end SourceSelection

namespace SelectedWitness
variable {H L L₁ T V V₃ V₁ : Subgroup G}
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    {ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁)}

/-- The actual conjugated subgroup, with its ambient quotient kernel retained. -/
def alpha (w : SelectedWitness L T H V L₁ V₃ V₁ ρ) : Subgroup G :=
  w.pair.Vgamma.map (MulAut.conj (w.conjugator : G)).toMonoidHom

omit [Finite G] in
/-- The selected conjugate remains inside H. -/
theorem alpha_le (w : SelectedWitness L T H V L₁ V₃ V₁ ρ) : w.alpha ≤ H := by
  rintro _ ⟨x, hx, rfl⟩
  exact H.mul_mem (H.mul_mem w.conjugator.property (w.actor_le hx))
    (H.inv_mem w.conjugator.property)

/-- Transport the actual local two-core, rather than dropping the kernel of
H → H/O₂(H), in the selected endpoint placement. -/
theorem alpha_star_le_core (w : SelectedWitness L T H V L₁ V₃ V₁ ρ)
    (hL₁ : L₁ ≤ H) (hT : T ≤ H) :
    Source.starImage H w.alpha ≤
      (Source.starImage H L₁ ⊔ Source.starImage H T).pCoreIn 2 := by
  have hh : Source.starImage H w.alpha ≤ Source.starImage H ((L₁ ⊔ T).pCoreIn 2) :=
    map_mono (subgroupOf_mono H w.conjugate_le_core)
  rw [ComponentSieve.Seven.LocalGeometry.starImage_twoCore H
    (L₁ ⊔ T) (sup_le hL₁ hT)] at hh
  simpa only [Source.starImage, subgroupOf_sup hL₁ hT, Subgroup.map_sup] using hh

/-- The actual H-conjugate vertex of the selected endpoint. -/
def alphaVertex (w : SelectedWitness L T H V L₁ V₃ V₁ ρ) : Vertex L T H :=
  inG0 (L := L) (T := T) w.conjugator • w.pair.gamma

omit [Finite G] in
/-- The composed endpoint transporter takes the base H-vertex to alpha. -/
theorem alphaVertex_eq (w : SelectedWitness L T H V L₁ V₃ V₁ ρ) :
    w.alphaVertex = (inG0 (L := L) (T := T) w.conjugator * w.pair.gb) •
      base L T H true := by
  rw [mul_smul, w.pair.gb_one]
  rfl

omit [Finite G] in
/-- The alpha subgroup is the VH-conjugate associated with this same
composed endpoint transporter. -/
theorem alpha_eq_endpoint_conjugate (w : SelectedWitness L T H V L₁ V₃ V₁ ρ) :
    w.alpha = (Source.VH H V).map
      (MulAut.conj ((w.conjugator : G) * (w.pair.gb : G))).toMonoidHom := by
  rw [alpha, CriticalGeometry.CriticalPair.Vgamma, map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    mul_inv_rev, mul_assoc]
end SelectedWitness

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.CriticalInputs

end
