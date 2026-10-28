module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Identification.Block.Complement

/-!
# The complement has the literal plane-radical image

Conjugate the full SL₃ covering map by the same alignment defining the
original flag. The proved radical operators are precisely two-parameter
shears. Equality of the actual P and R₂ action images transfers every
such shear to P, identifying the image of PV/V with the entire plane
radical in this fixed special-linear model.

Source: Aschbacher--Smith, refs/quasithin.pdf, printed p.774,
first three paragraphs. The exceptional model calculation uses I.2.2(3b).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open scoped IsMulCommutative commutatorElement MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.OriginalBlock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G} {h : G}
variable (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

open scoped MatrixGroups
open Matrix.PSL3.LinearThree

/-- The full special-linear cover in the one basis defining the source flag. -/
def alignedSeedModel : SeedQuotient D →* SL(3,S.field.Carrier) :=
  (MulAut.conj (SL3.alignment D S a)⁻¹).toMonoidHom.comp (seedQuotientModel D S a)

theorem alignedSeedModel_mk (l : L) :
    alignedSeedModel D S a (seedProjection D l) = SL3.PlaneAction.alignedQuotient D S a l := rfl

include D S a in
theorem alignedSeedModel_radical_operator (r : L) (hr : (r : G) ∈ (SL3.flag D S a).Ri 1)
    (v : Fin 3 → S.field.Carrier) :
    specialLinearNatural 3 (alignedSeedModel D S a (seedProjection D r)) v =
      SL3.RadicalAction.radicalOperator D S a ⟨r,hr⟩ v :=
  (SL3.RadicalAction.alignedAction_component D S a r v).symm

include D S a in
/-- The image of the literal complement is exactly the two-parameter shear group. -/
theorem pairImage_model_iff_shear
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hk : outsideResidual H ≤ pairGroup V h)
    (c : PairNaturalMarking V H h S.field) (hm : c.multiplicity = 2)
    (hB : axis V H = (SL3.flag D S a).Vi 1)
    (hPL : pairCore V H h ≤ L) (g : SL(3,S.field.Carrier)) :
    g ∈ (pairImage D H h).map (alignedSeedModel D S a) ↔
      ∃ x y : S.field.Carrier, ∀ v : Fin 3 → S.field.Carrier,
        g.val *ᵥ v = ![v 0+x*v 2,v 1+y*v 2,v 2] := by
  have hz := pair_intersection_eq_bot s hf hk
  have hPR := pairCore_le_plane_radical a (SL3.flag D S a) s hh hz hB
  have hact := pairCore_action_eq_radical a (SL3.flag D S a) s hh hf hk c hm hB
  constructor
  · rintro ⟨_,⟨p,hp,rfl⟩,rfl⟩
    obtain ⟨x,y,he⟩ := SL3.RadicalAction.radicalOperator_shear D S a ⟨p,hPR hp⟩
    exact ⟨x,y,fun v => (alignedSeedModel_radical_operator D S a p (hPR hp) v).trans (he v)⟩
  · rintro ⟨x,y,hg⟩
    obtain ⟨r,hr⟩ := SL3.RadicalAction.radicalOperator_realizes D S a x y
    obtain ⟨p,hp⟩ := hact.ge (show
      V.normalizerMonoidHom (inclusion
        ((localRadical_le_sylow (L := L) ((SL3.flag D S a).Vi 1)).trans S.sylow_normalizes) r)
        ∈ _ from ⟨r,rfl⟩)
    let pL : L := inclusion hPL p
    refine ⟨seedProjection D pL,mem_map_of_mem _ p.property,?_⟩
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro v
    change specialLinearNatural 3 (alignedSeedModel D S a (seedProjection D pL)) v = g.val *ᵥ v
    rw [alignedSeedModel_radical_operator D S a pL (hPR p.property),hg,←hr]
    obtain ⟨w,hw⟩ := (SL3.RadicalAction.vectorEquiv D S a).surjective (Multiplicative.ofAdd v)
    have he := congrArg (fun u : MulAut V => (SL3.RadicalAction.vectorEquiv D S a (u w)).toAdd) hp
    have hc (r : (SL3.flag D S a).Ri 1) :
        (SL3.RadicalAction.vectorEquiv D S a (V.normalizerMonoidHom
          (inclusion ((localRadical_le_sylow (L := L) ((SL3.flag D S a).Vi 1)).trans
            S.sylow_normalizes) r) w)).toAdd =
          SL3.RadicalAction.radicalOperator D S a r (SL3.RadicalAction.vectorEquiv D S a w).toAdd :=
      SL3.RadicalAction.alignedAction_projection D S a
        (SL3.RadicalAction.radicalInclusion D S a r) w
    change (SL3.RadicalAction.vectorEquiv D S a (V.normalizerMonoidHom
      (inclusion ((localRadical_le_sylow (L := L) ((SL3.flag D S a).Vi 1)).trans
        S.sylow_normalizes) ⟨p,hPR p.property⟩) w)).toAdd = _ at he
    have hsame : (⟨(pL : G),hPR p.property⟩ : (SL3.flag D S a).Ri 1) =
        ⟨(p : G),hPR p.property⟩ := rfl
    rw [hsame]
    simpa only [hc,hw,toAdd_ofAdd] using he

private def shearLocal (x y : S.field.Carrier) : lineLocalSL S.field.Carrier :=
  affineToLine S.field.Carrier (SemidirectProduct.inl (Multiplicative.ofAdd ![x,y]))

private theorem shearLocal_action (x y : S.field.Carrier) (v : Fin 3 → S.field.Carrier) :
    (shearLocal D S x y).val.val *ᵥ v = ![v 0+x*v 2,v 1+y*v 2,v 2] := by
  ext i
  fin_cases i <;> simp [shearLocal,affineToLine,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

private theorem shear_iff_lineRadical (g : SL(3,S.field.Carrier)) :
    (∃ x y : S.field.Carrier, ∀ v : Fin 3 → S.field.Carrier,
      g.val *ᵥ v = ![v 0+x*v 2,v 1+y*v 2,v 2]) ↔
    g ∈ (lineRadicalSL S.field.Carrier).map (lineLocalSL S.field.Carrier).subtype := by
  constructor
  · rintro ⟨x,y,hg⟩
    have he : (shearLocal D S x y).val = g := by
      apply Matrix.SpecialLinearGroup.toLin'_injective
      apply LinearEquiv.ext
      intro v
      exact (shearLocal_action D S x y v).trans (hg v).symm
    refine ⟨shearLocal D S x y,?_,he⟩
    exact (mem_lineRadicalSL_iff S.field.Carrier (shearLocal D S x y)).mpr
      ⟨rfl,rfl,rfl,rfl⟩
  · rintro ⟨g,hg,rfl⟩
    obtain ⟨h00,h01,h10,h11⟩ := (mem_lineRadicalSL_iff S.field.Carrier g).mp hg
    obtain ⟨h20,h21,h22⟩ := (mem_lineLocalSL_iff S.field.Carrier g.val).mp g.property
    refine ⟨g.val.val 0 2,g.val.val 1 2,fun v => ?_⟩
    ext i
    fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_three,h00,h01,h10,h11,h20,h21,h22]

include D S a in
/-- The complement maps onto the literal radical of the original plane parabolic. -/
theorem pairImage_model_eq_lineRadical
    (s : Hypothesis1131At D S U₁ H) (hh : h ∈ H)
    (hf : omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) = ⊥)
    (hk : outsideResidual H ≤ pairGroup V h)
    (c : PairNaturalMarking V H h S.field) (hm : c.multiplicity = 2)
    (hB : axis V H = (SL3.flag D S a).Vi 1)
    (hPL : pairCore V H h ≤ L) :
    (pairImage D H h).map (alignedSeedModel D S a) =
      (lineRadicalSL S.field.Carrier).map (lineLocalSL S.field.Carrier).subtype := by
  ext g
  exact (pairImage_model_iff_shear D S a s hh hf hk c hm hB hPL g).trans
    (shear_iff_lineRadical D S g)


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.OriginalBlock
