module

public import Theory.SpecificGroups.SymmetricSix.PolarAffine.Cocycles
public import Theory.Representation.SL2NaturalFirstCohomology
public import Theory.Representation.SL2FourNaturalOrbits.Model

/-!
# The exact restriction test for an endpoint displacement

A displacement on a subgroup extends to the six-letter A₆ action precisely
when it is the restriction of one binary quadratic parameter plus a principal
vector. For an actual natural SL₂(4) endpoint, not every cocycle passes this
test: its first cohomology has four elements, while the ambient restriction
has at most two. The statement keeps the actual embedding and action marking.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymmetricSix.PolarAffine
open Representation Representation.OneCohomology

private def polarRep : Representation (ZMod 2) A6 NaturalModule where
  toFun g := polarLinearMap g.val
  map_one' := LinearMap.ext fun v => polarAction_one v
  map_mul' g h := LinearMap.ext fun v => polarAction_mul g.val h.val v

/-- A subgroup cocycle extends exactly when its marked values have the ambient
binary quadratic normal form. No unrestricted extension assertion is used. -/
theorem restriction_extends_iff {H : Type*} [Group H] (ι : H →* A6)
    (f : H → NaturalModule) :
    (∃ δ : A6 → NaturalModule,
      (∀ g h, δ (g*h)=polarAction g.val (δ h)+δ g) ∧
      ∀ h, δ (ι h)=f h) ↔
    ∃ (b : ZMod 2) (v : NaturalModule),
      ∀ h, f h=b • quadratic (ι h)+(polarAction (ι h).val v-v) := by
  constructor
  · rintro ⟨δ,hδ,hr⟩
    obtain ⟨b,v,hv⟩ := cocycle_normal_form δ hδ
    exact ⟨b,v,fun h => (hr h).symm.trans (hv (ι h))⟩
  · rintro ⟨b,v,hv⟩
    let Q : cocycles polarRep := ⟨quadratic,quadratic_mul⟩
    let δ : cocycles polarRep := b • Q + principal polarRep v
    exact ⟨δ.val,δ.property,fun h => (hv h).symm⟩

local notation "F" => SL2FourNatural.F
local notation "V" => SL2FourNatural.V
local notation "SL" => SL2FourNatural.SL
local notation "natRep" => (specialLinearNatural (k := SL2FourNatural.F) 2)

/-- Even for the same actual naturally marked A₅ endpoint, universal cocycle
extension to the A₆ polar action is false. The remaining marking must meet the
specific restriction criterion, not merely be a natural endpoint. -/
theorem not_all_natural_endpoint_cocycles_extend
    (ι : SL →* A6) (e : NaturalModule ≃ₗ[ZMod 2] V)
    (he : ∀ (g : SL) (v : NaturalModule),
      e (polarAction (ι g).val v)=SL2FourNatural.action g (e v)) :
    ¬ ∀ f : cocycles natRep, ∃ δ : A6 → NaturalModule,
      (∀ g h, δ (g*h)=polarAction g.val (δ h)+δ g) ∧
      ∀ g, e (δ (ι g))=f.val g := by
  intro hall
  let Q : cocycles natRep := ⟨fun g => e (quadratic (ι g)),by
    intro g h
    change e (quadratic (ι (g*h))) =
      specialLinearNatural 2 g (e (quadratic (ι h))) + e (quadratic (ι g))
    rw [map_mul,quadratic_mul,map_add,he,SL2FourNatural.action_natural]⟩
  have hc (z : H1 natRep) : z=0 ∨ z=classMap natRep Q := by
    obtain ⟨f,rfl⟩ := (principal natRep).range.mkQ_surjective z
    obtain ⟨δ,hδ,hf⟩ := hall f
    obtain ⟨b,v,hv⟩ := cocycle_normal_form δ hδ
    have hval (g : SL) := congrArg e (hv (ι g))
    have hb : b=0 ∨ b=1 := by
      have hall : ∀ c : ZMod 2, c=0 ∨ c=1 := by decide +kernel
      exact hall b
    rcases hb with rfl | rfl
    · left
      apply (classMap_eq_zero_iff natRep f).mpr
      refine ⟨e v,Subtype.ext (funext fun g => ?_)⟩
      have hh := hval g
      simp only [zero_smul,zero_add,map_sub,he,hf] at hh
      change specialLinearNatural 2 g (e v)-e v=f.val g
      simpa only [SL2FourNatural.action_natural] using hh.symm
    · right
      have hfeq : f=Q+principal natRep (e v) := by
        apply Subtype.ext
        funext g
        have hh := hval g
        change f.val g=e (quadratic (ι g))+(specialLinearNatural 2 g (e v)-e v)
        simpa only [one_smul,map_add,map_sub,he,hf,SL2FourNatural.action_natural] using hh
      change classMap natRep f = _
      rw [hfeq,map_add,(classMap_eq_zero_iff natRep _).mpr ⟨e v,rfl⟩,add_zero]
  have hF : 2 < Nat.card F := by
    rw [Nat.card_eq_fintype_card,SL2FourNatural.card_field]
    decide
  let E := SL2NaturalH1.cohomologyEquiv (K := F) hF
  have htwo (x : F) : x=0 ∨ x=E (classMap natRep Q) := by
    rcases hc (E.symm x) with hx | hx
    · left
      have hh := congrArg E hx
      simpa only [LinearEquiv.apply_symm_apply,map_zero] using hh
    · right
      have hh := congrArg E hx
      simpa only [LinearEquiv.apply_symm_apply] using hh
  have h1 := (htwo 1).resolve_left one_ne_zero
  let w : F := ⟨0,1⟩
  have hw0 : w≠0 := by decide +kernel
  have hw1 : w≠1 := by decide +kernel
  exact hw1 (((htwo w).resolve_left hw0).trans h1.symm)

end Theory.SpecificGroups.SymmetricSix.PolarAffine
