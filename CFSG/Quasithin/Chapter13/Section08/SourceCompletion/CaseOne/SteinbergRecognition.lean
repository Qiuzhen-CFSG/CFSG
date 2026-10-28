module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.Irreducible
public import Theory.Representation.BinaryAlternatingSixModels.ParabolicPlanes
public import Theory.Representation.Quotient
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.SourceAssembly
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis33.ChiefFiltrations.Steinberg

/-!
# Recognizing the actual Steinberg quotient from the two source planes

Each irreducible local plane generates U_L/V under the full barred group,
so both inject into a common irreducible quotient. The actual H1 and H2
markings allow the proved binary S₆ catalogue to identify that quotient
with the sixteen-dimensional tensor. Composing with the literal U_L/V
projection constructs its group quotient and its precise kernel E≥V.
Equivariance retains the common cubic actor and the outer marking.

`source_tensor_section` applies this to the actual SourceLocalPlanes output
of 13.8.6(4). Its construction from all earlier inputs, the local parabolic
markings and the later abelian branch remain source-assembly obligations.
CaseOne.SteinbergComparison is the actual nonabelian consumer. Final
13.8.33 remains with qt-d-138-a6-endgame-source; the original ordinary
configuration remains with qt-d-138-six-g2-source.
Source: Aschbacher--Smith, G.5.2,13.8.6(4),13.8.33, pp.343,948,967.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionQuotients BinaryAlternatingSix Theory.SpecificGroups.SymmetricSix

variable {B X : Type*} [Group B] [AddCommGroup X] [Module (ZMod 2) X]

/-- The two original local planes force an actual Steinberg quotient. -/
private theorem tensor_quotient_of_local_planes [Finite X] [Nontrivial X]
    (ρ : Representation (ZMod 2) B X) (e : B ≃* S6)
    (P₁ P₂ : Subgroup B)
    (S₁ : Subrepresentation (ρ.comp P₁.subtype))
    (S₂ : Subrepresentation (ρ.comp P₂.subtype))
    [IsIrreducible S₁.toRepresentation] [IsIrreducible S₂.toRepresentation]
    (hgen₁ : Submodule.span (ZMod 2) {x | ∃ a : B, ∃ s : S₁, x = ρ a (s : X)} = ⊤)
    (hgen₂ : Submodule.span (ZMod 2) {x | ∃ a : B, ∃ s : S₂, x = ρ a (s : X)} = ⊤)
    (hdim₁ : Module.finrank (ZMod 2) S₁.toSubmodule = 2)
    (hdim₂ : Module.finrank (ZMod 2) S₂.toSubmodule = 2)
    (hP₁ : ∀ g ∈ BinaryFlags.H1, e.symm g ∈ P₁)
    (hP₂ : ∀ g ∈ BinaryFlags.H2, e.symm g ∈ P₂) :
    ∃ q : ρ.IntertwiningMap (tensorAction.comp e.toMonoidHom), Function.Surjective q := by
  obtain ⟨W, hW, hi⟩ := exists_irreducible_quotient ρ
  let := hi
  let τ := W.quotientRepresentation.comp e.symm.toMonoidHom
  let : IsIrreducible τ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      W.quotientRepresentation).mpr hi
  have h₁ : HasInvariantLine τ BinaryFlags.H1 := by
    refine ⟨(localQuotientMap ρ P₁ S₁ W).range.toSubmodule,
      localQuotientMap_finrank ρ P₁ S₁ hgen₁ W hW hdim₁, ?_⟩
    intro g hg v hv
    exact (localQuotientMap ρ P₁ S₁ W).range.apply_mem_toSubmodule
      ⟨e.symm g, hP₁ g hg⟩ hv
  have h₂ : HasInvariantLine τ BinaryFlags.H2 := by
    refine ⟨(localQuotientMap ρ P₂ S₂ W).range.toSubmodule,
      localQuotientMap_finrank ρ P₂ S₂ hgen₂ W hW hdim₂, ?_⟩
    intro g hg v hv
    exact (localQuotientMap ρ P₂ S₂ W).range.apply_mem_toSubmodule
      ⟨e.symm g, hP₂ g hg⟩ hv
  obtain ⟨F⟩ := tensor_of_parabolic_planes τ h₁ h₂
  let q : ρ.IntertwiningMap (tensorAction.comp e.toMonoidHom) := {
    toLinearMap := F.toLinearMap.comp W.toSubmodule.mkQ
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro v
      change F (W.toSubmodule.mkQ (ρ g v)) = tensorAction (e g) (F (W.toSubmodule.mkQ v))
      have he := IntertwiningMap.isIntertwining _ _ F.toIntertwiningMap
        (e g) (W.toSubmodule.mkQ v)
      change F (W.quotientRepresentation (e.symm (e g)) (W.toSubmodule.mkQ v)) =
        tensorAction (e g) (F (W.toSubmodule.mkQ v)) at he
      simpa only [e.symm_apply_apply, Subrepresentation.quotientRepresentation_mk] using he }
  exact ⟨q, F.toLinearEquiv.surjective.comp W.toSubmodule.mkQ_surjective⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne

namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionQuotients TransvectionQuotients.FourLocalFactors
open A6Endgame.ActionAnalysis33.ChiefModels
open BinaryAlternatingSix Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G]
  {L H T L₁ L₂ V V₂ V₃ : Subgroup G}

/-- Recognition on the literal bar image, using the constructed source planes. -/
theorem source_tensor_quotient
    (d : SectionStructure.Data L H T L₁ L₂ V V₂ V₃)
    (e : (barMap (L ⊔ T) V d.normalizes_V).range ≃* S6)
    (e₁ : ((((L₁ ⊔ T).subgroupOf (L ⊔ T)).map
      (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict) ⧸
      pCore 2 (((L₁ ⊔ T).subgroupOf (L ⊔ T)).map
      (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict)) ≃* Equiv.Perm (Fin 3))
    (e₂ : ((((L₂ ⊔ T).subgroupOf (L ⊔ T)).map
      (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict) ⧸
      pCore 2 (((L₂ ⊔ T).subgroupOf (L ⊔ T)).map
      (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict)) ≃* Equiv.Perm (Fin 3))
    (hp : SourceLocalPlanes d e₁ e₂)
    (hP₁ : ∀ g ∈ BinaryFlags.H1, e.symm g ∈
      ((L₁ ⊔ T).subgroupOf (L ⊔ T)).map (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict)
    (hP₂ : ∀ g ∈ BinaryFlags.H2, e.symm g ∈
      ((L₂ ⊔ T).subgroupOf (L ⊔ T)).map (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict) :
    let _ := d.normal
    let _ := d.elementary
    ∃ q : d.action.IntertwiningMap (tensorAction.comp e.toMonoidHom), Function.Surjective q := by
  let _ := d.normal
  let _ := d.elementary
  let π := (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict
  let P₁ := ((L₁ ⊔ T).subgroupOf (L ⊔ T)).map π
  let P₂ := ((L₂ ⊔ T).subgroupOf (L ⊔ T)).map π
  let S₁ := localImage (Source.UL L H V₃) V (L ⊔ T) π d.normalizes_UL d.action d.conjugation
    (L₁ ⊔ T) (Source.UH H V₃) d.normalizes_UH
  let S₂ := localImage (Source.UL L H V₃) V (L ⊔ T) π d.normalizes_UL d.action d.conjugation
    (L₂ ⊔ T) (Source.U2 H V V₂) d.normalizes_U2
  obtain ⟨h₁,h₂,hgen₁,hgen₂,_⟩ := hp
  let : IsIrreducible S₁.toRepresentation := h₁.2.1
  let : IsIrreducible S₂.toRepresentation := h₂.2.1
  have hd₁ : Module.finrank (ZMod 2) S₁.toSubmodule = 2 := h₁.1
  let : Nontrivial (Additive (Source.ULsection L H V₃ V)) :=
    Module.nontrivial_of_finrank_pos (lt_of_lt_of_le (by omega : 0 < Module.finrank (ZMod 2) S₁.toSubmodule)
      S₁.toSubmodule.finrank_le)
  exact tensor_quotient_of_local_planes d.action e P₁ P₂ S₁ S₂
    hgen₁ hgen₂ h₁.1 h₂.1 hP₁ hP₂

variable {B : Type*} [Group B]

omit [Finite G] in
/-- Convert the recognized module quotient to the actual group section.
The denominator is constructed as the inverse image of the linear kernel. -/
theorem tensor_section_of_quotient
    (A P R N : Subgroup G) [(N.subgroupOf R).Normal]
    [IsElementaryAbelian 2 (R ⧸ N.subgroupOf R)]
    (hNR : N ≤ R) (hAP : A ≤ P) (π : P →* B)
    (hPR : P ≤ normalizer (R : Set G))
    (ρ : Representation (ZMod 2) B (Additive (R ⧸ N.subgroupOf R)))
    (hρ : SectionConjugationAlong P R N π hPR ρ)
    (e : B ≃* S6)
    (q : ρ.IntertwiningMap (tensorAction.comp e.toMonoidHom)) (hq : Function.Surjective q)
    (f : A →* cubicActor)
    (hmark : ∀ a : A, e (π (inclusion hAP a)) = (cubicActorEquiv (f a) : S6)) :
    ∃ E : Subgroup G, N ≤ E ∧ Nonempty (OppositeTensorSection A E R f) := by
  let E := sectionPreimage R N q.toLinearMap.ker
  let φ : R →* Multiplicative TensorModule :=
    q.toLinearMap.toAddMonoidHom.toMultiplicativeRight.comp (QuotientGroup.mk' (N.subgroupOf R))
  have hφ : Function.Surjective φ := by
    intro v
    obtain ⟨x,hx⟩ := hq v.toAdd
    obtain ⟨r,hr⟩ := QuotientGroup.mk'_surjective (N.subgroupOf R) x.toMul
    refine ⟨r, ?_⟩
    change q (Additive.ofMul (QuotientGroup.mk' (N.subgroupOf R) r)) = v.toAdd
    rw [hr]
    exact hx
  have hk : φ.ker = E.subgroupOf R := by
    ext r
    change q (Additive.ofMul (QuotientGroup.mk' (N.subgroupOf R) r)) = 0 ↔ (r : G) ∈ E
    exact (mem_sectionPreimage R N q.toLinearMap.ker r).symm
  let _ := Representation.BinaryFixedPoints.action (tensorAction.comp duadCubicActor.subtype)
  refine ⟨E, denominator_le_sectionPreimage R N hNR q.toLinearMap.ker,
    ⟨⟨sectionPreimage_le R N _, hAP.trans hPR, φ, hφ, hk, ?_⟩⟩⟩
  let _ := conjMulDistribMulActionOfLeNormalizer A R (hAP.trans hPR)
  intro a r
  change q (Additive.ofMul (QuotientGroup.mk' (N.subgroupOf R) (a • r))) =
    tensorAction (cubicActorEquiv (f a) : S6)
      (q (Additive.ofMul (QuotientGroup.mk' (N.subgroupOf R) r)))
  have hc : Additive.ofMul (QuotientGroup.mk' (N.subgroupOf R) (a • r)) =
      ρ (π (inclusion hAP a)) (Additive.ofMul (QuotientGroup.mk' (N.subgroupOf R) r)) :=
    (hρ (inclusion hAP a) r).symm
  rw [hc]
  have he := IntertwiningMap.isIntertwining _ _ q (π (inclusion hAP a))
    (Additive.ofMul (QuotientGroup.mk' (N.subgroupOf R) r))
  change q (ρ (π (inclusion hAP a)) _) = tensorAction (e (π (inclusion hAP a))) _ at he
  rwa [hmark] at he

/-- The original two local planes construct the literal tensor section and its kernel. -/
theorem source_tensor_section
    (d : SectionStructure.Data L H T L₁ L₂ V V₂ V₃)
    (e : (barMap (L ⊔ T) V d.normalizes_V).range ≃* S6)
    (e₁ : ((((L₁ ⊔ T).subgroupOf (L ⊔ T)).map
      (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict) ⧸
      pCore 2 (((L₁ ⊔ T).subgroupOf (L ⊔ T)).map
      (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict)) ≃* Equiv.Perm (Fin 3))
    (e₂ : ((((L₂ ⊔ T).subgroupOf (L ⊔ T)).map
      (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict) ⧸
      pCore 2 (((L₂ ⊔ T).subgroupOf (L ⊔ T)).map
      (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict)) ≃* Equiv.Perm (Fin 3))
    (hp : SourceLocalPlanes d e₁ e₂)
    (hP₁ : ∀ g ∈ BinaryFlags.H1, e.symm g ∈
      ((L₁ ⊔ T).subgroupOf (L ⊔ T)).map (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict)
    (hP₂ : ∀ g ∈ BinaryFlags.H2, e.symm g ∈
      ((L₂ ⊔ T).subgroupOf (L ⊔ T)).map (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict)
    (A : Subgroup G) (hAL : A ≤ L ⊔ T) (f : A →* cubicActor)
    (hmark : ∀ a : A,
      e ((barMap (L ⊔ T) V d.normalizes_V).rangeRestrict (inclusion hAL a)) =
        (cubicActorEquiv (f a) : S6)) :
    ∃ E : Subgroup G, V ≤ E ∧ Nonempty (OppositeTensorSection A E (Source.UL L H V₃) f) := by
  let _ := d.normal
  let _ := d.elementary
  obtain ⟨q,hq⟩ := source_tensor_quotient d e e₁ e₂ hp hP₁ hP₂
  exact tensor_section_of_quotient A (L ⊔ T) (Source.UL L H V₃) V
    d.contains hAL (barMap (L ⊔ T) V d.normalizes_V).rangeRestrict
    d.normalizes_UL d.action d.conjugation e q hq f hmark

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
