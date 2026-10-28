module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.SourceSections
public import Theory.Representation.BinaryOffender.QuadraticImageBound
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.Homogeneous.Basic
/-!
# The same quadratic actor on both source orbit spans

Let K be a component, A an elementary quadratic actor faithful on the
T-orbit of K, and I a genuine noncentral Irr⁺ seed. For every intermediate
acting subgroup X containing K and T, the kernel on the actual X-span
of I centralizes the component orbit. Consequently A, when contained in
X, remains faithful on that span. Restriction decreases fixed codimension
and preserves the actor's order; the literal action image is therefore a
quadratic member with ratio at most two, also for the cubic ratio.

Taking X=K₀T or the whole actor gives the unchanged T- and H-spans in
F.9.18(3). No module classification or faithfulness-on-span premise is used.
Source: Aschbacher--Smith, F.9.18(3), printed p.325.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.F918
open Components.Swapped.LinearTwo.ModuleAlternatives
open Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
/-- Literal action data for the same elementary actor on an orbit span. -/
structure SpanActorResult {D E:Type*} [Group D] [AddCommGroup E] [Module (ZMod 2) E]
    (ρ:Representation (ZMod 2) D E) (A X:Subgroup D) (I:Submodule (ZMod 2) E) : Prop where
  faithful : ∀a∈A.subgroupOf X, (∀v,(seedSpan (ρ.comp X.subtype) I).toRepresentation a v=v)→a=1
  equiv : Nonempty (A≃*actionSubgroup (seedSpan (ρ.comp X.subtype) I).toRepresentation (A.subgroupOf X))
  elementary : IsElementaryTwo (actionSubgroup (seedSpan (ρ.comp X.subtype) I).toRepresentation (A.subgroupOf X))
  quadratic : IsQuadratic (imageRepresentation (seedSpan (ρ.comp X.subtype) I).toRepresentation)
    (actionSubgroup (seedSpan (ρ.comp X.subtype) I).toRepresentation (A.subgroupOf X))
  bound : fixedCodim (imageRepresentation (seedSpan (ρ.comp X.subtype) I).toRepresentation)
    (actionSubgroup (seedSpan (ρ.comp X.subtype) I).toRepresentation (A.subgroupOf X)) ≤
      2*rank (actionSubgroup (seedSpan (ρ.comp X.subtype) I).toRepresentation (A.subgroupOf X))
  quadratic_ratio : quadraticRatio (imageRepresentation (seedSpan (ρ.comp X.subtype) I).toRepresentation)≤2
  cubic_ratio : cubicRatio (imageRepresentation (seedSpan (ρ.comp X.subtype) I).toRepresentation)≤2

section Names
variable {D E:Type*} [Group D] [AddCommGroup E] [Module (ZMod 2) E]
 (ρ:Representation (ZMod 2) D E)
open Representation.BinaryOffender.Homogeneous

/-- The old source span and the D.3 orbit span are the identical subspace. -/
theorem seedSpan_eq_orbitSpan (X:Subgroup D) (I:Submodule (ZMod 2) E) :
    (seedSpan (ρ.comp X.subtype) I).toSubmodule=orbitSpan ρ X I := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨x,w,hw,rfl⟩
    exact Submodule.mem_iSup_of_mem x (Submodule.mem_map_of_mem hw)
  · apply iSup_le
    intro x
    rintro v ⟨w,hw,rfl⟩
    exact Submodule.subset_span ⟨x,w,hw,rfl⟩

/-- A component-invariant seed has the same span under K₀T as under T. -/
theorem seedSpan_join_eq_T_span (K₀ T:Subgroup D) (I:Submodule (ZMod 2) E)
    (hn:T≤normalizer (K₀:Set D)) (hI:IsIrrPlus ρ K₀ I) :
    (seedSpan (ρ.comp (K₀⊔T).subtype) I).toSubmodule=orbitSpan ρ T I := by
  rw [seedSpan_eq_orbitSpan]
  apply le_antisymm
  · exact orbitSpan_le ρ (le_orbitSpan ρ T I)
      (sup_le (orbitSpan_component_invariant ρ hn hI) (orbitSpan_invariant ρ T I))
  · exact orbitSpan_le ρ (le_orbitSpan ρ (K₀⊔T) I)
      (le_sup_right.trans (orbitSpan_invariant ρ (K₀⊔T) I))
end Names

variable {D E:Type*} [Group D] [Finite D] [AddCommGroup E] [Module (ZMod 2) E]
 [FiniteDimensional (ZMod 2) E]
 (ρ:Representation (ZMod 2) D E) (K T A X:Subgroup D)
 (hK:Theory.GroupTheory.IsComponent D K) (hKX:K≤X) (hTX:T≤X) (hAX:A≤X)
 (hA:IsElementaryTwo A) (hq:IsQuadratic ρ A) (hbound:fixedCodim ρ A≤2*rank A)
 (hfaith:A⊓centralizer (conjugateSpanBy K T:Set D)=⊥)
 (I:Submodule (ZMod 2) E) (hI:IsIrrPlus ρ (conjugateSpanBy K T) I)
include hK hKX hTX hI in
omit [Finite D] [FiniteDimensional (ZMod 2) E] in
theorem orbit_span_kernel_centralizes :
    (actionHom (seedSpan (ρ.comp X.subtype) I).toRepresentation).ker ≤
      centralizer (conjugateSpanBy (K.subgroupOf X) (T.subgroupOf X):Set X) := by
  apply action_kernel_le_centralizer_of_component_orbit _ _ _ (hK.subgroupOf hKX)
  intro hall
  apply hI.not_le_fixedSpace ρ
  have horbit:=subgroupOf_conjugateSpan X K T hKX hTX
  have hOX:conjugateSpanBy K T≤X:=conjugateSpanBy_le hKX (hTX.trans X.le_normalizer)
  intro v hv l
  have hl:(⟨l,hOX l.property⟩:X)∈conjugateSpanBy (K.subgroupOf X) (T.subgroupOf X):=horbit ▸ l.property
  have hvJ:v∈(seedSpan (ρ.comp X.subtype) I).toSubmodule:=le_seedSpan (ρ.comp X.subtype) I hv
  exact congrArg (fun w:seedSpan (ρ.comp X.subtype) I=>(w:E)) (hall ⟨l,hOX l.property⟩ hl ⟨v,hvJ⟩)

include hK hKX hTX hAX hA hq hbound hfaith hI
omit [Finite D] in
theorem faithful_quadratic_orbit_span :
    let σ:=(seedSpan (ρ.comp X.subtype) I).toRepresentation
    (∀ a∈A.subgroupOf X,(∀v,σ a v=v)→a=1) ∧
      Nonempty (A≃*actionSubgroup σ (A.subgroupOf X)) ∧
      IsElementaryTwo (actionSubgroup σ (A.subgroupOf X)) ∧
      IsQuadratic (imageRepresentation σ) (actionSubgroup σ (A.subgroupOf X)) ∧
      fixedCodim (imageRepresentation σ) (actionSubgroup σ (A.subgroupOf X))≤
        2*rank (actionSubgroup σ (A.subgroupOf X)) := by
  let J:=seedSpan (ρ.comp X.subtype) I
  let σ:=J.toRepresentation
  let KX:=K.subgroupOf X
  let TX:=T.subgroupOf X
  let AX:=A.subgroupOf X
  have horbit:(conjugateSpanBy K T).subgroupOf X=conjugateSpanBy KX TX:=
    subgroupOf_conjugateSpan X K T hKX hTX
  have hOX:conjugateSpanBy K T≤X:=conjugateSpanBy_le hKX (hTX.trans X.le_normalizer)
  have hker:=orbit_span_kernel_centralizes ρ K T X hK hKX hTX I hI
  have hf:∀a∈AX,(∀v,σ a v=v)→a=1 := by
    intro a ha hv
    have hc:=hker ((actionHom_eq_one_iff σ a).mpr hv)
    have hc':(a:D)∈centralizer (conjugateSpanBy K T:Set D) := by
      intro x hx
      have hx':(⟨x,hOX hx⟩:X)∈conjugateSpanBy KX TX:=horbit ▸ hx
      exact congrArg Subtype.val (hc ⟨x,hOX hx⟩ hx')
    exact Subtype.ext (mem_bot.mp (hfaith ▸ (show (a:D)∈A⊓centralizer (conjugateSpanBy K T:Set D) from ⟨ha,hc'⟩)))
  have hAE:IsElementaryTwo AX := by
    let : IsElementaryAbelian 2 A:=hA.2
    refine ⟨?_,IsElementaryAbelian.of_surjective (subgroupOfEquivOfLe hAX).symm.toMonoidHom (subgroupOfEquivOfLe hAX).symm.surjective⟩
    intro he
    apply hA.1
    rw [←map_subgroupOf_eq_of_le hAX]
    change AX.map X.subtype=⊥
    rw [he,Subgroup.map_bot]
  have hr:rank AX=rank A := congrArg (Nat.log 2) (Nat.card_congr (subgroupOfEquivOfLe hAX).toEquiv)
  have hc:fixedCodim (ρ.comp X.subtype) AX=fixedCodim ρ A := by
    unfold fixedCodim
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le hAX]
  have hqx:IsQuadratic (ρ.comp X.subtype) AX := fun a ha b hb v=>hq a ha b hb v
  have hqJ:=quadratic_subrepresentation (ρ.comp X.subtype) J hqx
  refine ⟨hf,⟨(subgroupOfEquivOfLe hAX).symm.trans (faithfulActionEquiv σ AX hf)⟩,
    hAE.actionSubgroup σ hf,quadratic_actionSubgroup σ hqJ,?_⟩
  rw [fixedCodim_actionSubgroup,actionSubgroup_rank σ AX hf]
  exact (fixedCodim_subrepresentation_le (ρ.comp X.subtype) J AX).trans (by rwa [hc,hr])

theorem orbit_span_ratio_bounds :
    let σ:=(seedSpan (ρ.comp X.subtype) I).toRepresentation
    quadraticRatio (imageRepresentation σ)≤2 ∧ cubicRatio (imageRepresentation σ)≤2 := by
  have hh:=faithful_quadratic_orbit_span ρ K T A X hK hKX hTX hAX hA hq hbound hfaith I hI
  have hq':quadraticRatio (imageRepresentation (seedSpan (ρ.comp X.subtype) I).toRepresentation)≤2 :=
    (quadraticRatio_le_two_iff _).mpr ⟨_,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2⟩
  exact ⟨hq',(cubicRatio_le_quadraticRatio _).trans hq'⟩

/-- Bundle the faithful actor with its two unchanged ratio bounds. -/
theorem spanActorResult : SpanActorResult ρ A X I := by
  have hf:=faithful_quadratic_orbit_span ρ K T A X hK hKX hTX hAX hA hq hbound hfaith I hI
  have hr:=orbit_span_ratio_bounds ρ K T A X hK hKX hTX hAX hA hq hbound hfaith I hI
  exact ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2,hr.1,hr.2⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.F918
