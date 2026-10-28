module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.AlternatingSixMovementSource
public import Theory.SpecificGroups.AlternatingSix.MovingFourAutomizer
/-! # The actual A₆ component automizer alternatives
The original Sylow action supplies a moving four-group in its A₆ component.
The proved full automorphism geometry excludes the natural S₆ image and
leaves exactly M₁₀, PGL₂(9), or Aut(A₆). The quotient versions use the actual
normalizer conjugation map and its literal centralizer kernel.
Source: Aschbacher--Smith 2.5.16(3), printed p.560.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Theory.GroupTheory AlternatingSix.ShadowLocal
variable {G:Type*} [Group G] [Finite G] {M H:Subgroup G}
theorem alternating_six_normalizer_models
    (hH:H∈gammaZero (Chapter1.He G) M)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (S:Sylow 2 H) (hSM:(S:Subgroup H).map H.subtype≤M)
    (D:Subgroup H) (hD:IsComponent H D) (hout:¬D.map H.subtype≤M)
    (e:D≃*A6) :
    let f:=(MulAut.congr e).toMonoidHom.comp D.normalizerMonoidHom
    Nonempty (f.range≃*AlternatingSix.M10.extension) ∨
      Nonempty (f.range≃*GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) ∨
      Nonempty (f.range≃*AutA6) := by
  let f:=(MulAut.congr e).toMonoidHom.comp D.normalizerMonoidHom
  obtain ⟨P,hP⟩:=S.exists_subgroupOf_eq_of_subnormal D hD.1
  let Q:=P.mapSurjective (f:=e.toMonoidHom) e.surjective
  obtain ⟨E,hE,hEP,s,hs,hm⟩:=alternating_six_four_movement_source hH hempty S hSM D hD hout e
  let :=hE
  let F:=E.map e.toMonoidHom
  let eF:=E.equivMapOfInjective e.toMonoidHom e.injective
  let : IsKleinFour F:={
    card_four := (Nat.card_congr eF.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eF).symm.trans IsKleinFour.exponent_two }
  let N:=(S:Subgroup H)⊓normalizer (D:Set H)
  let g:N→*AutA6:=f.comp (inclusion inf_le_right)
  let A:=g.range
  have hA:IsPGroup 2 A:=(S.isPGroup'.to_le (show N≤S from inf_le_left)).of_surjective
    g.rangeRestrict g.rangeRestrict_surjective
  have hconj (d:D):f ⟨d,D.le_normalizer d.property⟩=MulAut.conj (e d):=by
    have hd:D.normalizerMonoidHom ⟨d,D.le_normalizer d.property⟩=MulAut.conj d:=by
      ext v
      rfl
    change MulAut.congr e (D.normalizerMonoidHom ⟨d,D.le_normalizer d.property⟩)=_
    rw [hd]
    exact MulAut.congr_conj e d
  have hQA:(Q:Subgroup A6).map MulAut.conj≤A:=by
    rintro _ ⟨_,⟨d,hd,rfl⟩,rfl⟩
    refine ⟨⟨d,(show d∈(S:Subgroup H).subgroupOf D from hP ▸ hd),D.le_normalizer d.property⟩,?_⟩
    exact hconj d
  have hFQ:F≤Q:=map_mono (hP.symm ▸ hEP)
  have hmove:∃a∈A,F.map a.toMonoidHom≠F:=by
    refine ⟨f s,⟨⟨s,hs,s.property⟩,rfl⟩,?_⟩
    intro he
    apply hm
    apply map_injective (f:=e.toMonoidHom) e.injective
    have hcomp:e.toMonoidHom.comp (D.normalizerMonoidHom s).toMonoidHom=
        (f s).toMonoidHom.comp e.toMonoidHom:=by
      ext u
      simp [f,MulAut.congr_apply]
    rw [map_map,hcomp,←map_map]
    exact he
  have hn:¬A≤natural:=not_le_natural_of_four_movement Q A hA hQA F hFQ hmove
  have hi:AlternatingSix.ShadowLocal.inner≤f.range:=by
    rintro _ ⟨a,rfl⟩
    exact ⟨⟨e.symm a,D.le_normalizer (e.symm a).property⟩,by
      rw [hconj,e.apply_symm_apply]⟩
  apply AlternatingSix.overgroup_not_natural_models f.range hi
  intro hf
  apply hn
  rintro _ ⟨n,rfl⟩
  exact hf ⟨inclusion inf_le_right n,rfl⟩

open ComponentRefinement
variable {L:Subgroup G} {S:Sylow 2 H} {z:G}
/-- The original relative component's literal action-image alternatives. -/
theorem MathieuSourceSetup.alternating_six_normalizer_models
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (e:L≃*A6) :
    let eD:=(subgroupOfEquivOfLe c.component_le).trans e
    let f:=(MulAut.congr eD).toMonoidHom.comp (L.subgroupOf H).normalizerMonoidHom
    Nonempty (f.range≃*AlternatingSix.M10.extension) ∨
      Nonempty (f.range≃*GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) ∨
      Nonempty (f.range≃*AutA6) := by
  let D:=L.subgroupOf H
  have hout:¬D.map H.subtype≤M:=((c.hypotheses115 hG).component_inputs D c.component).1
  exact CFSG.Quasithin.Chapter2.Section05.ComponentSelection.alternating_six_normalizer_models
    c.gamma hempty S (c.hypotheses115 hG).mem_HeOver.2.2 D c.component hout
    ((subgroupOfEquivOfLe c.component_le).trans e)

/-- The three literal normalizer quotients, without an assumed outer action. -/
theorem MathieuSourceSetup.alternating_six_normalizer_quotient
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (e:L≃*A6) :
    let D:=L.subgroupOf H
    let Q:=(normalizer (D:Set H)) ⧸
      (centralizer (D:Set H)).subgroupOf (normalizer (D:Set H))
    Nonempty (Q≃*AlternatingSix.M10.extension) ∨
      Nonempty (Q≃*GorensteinWalter.PGL2 Atlas.Comparisons.Exceptional.Nine.F) ∨
      Nonempty (Q≃*AutA6) := by
  let D:=L.subgroupOf H
  let eD:=(subgroupOfEquivOfLe c.component_le).trans e
  let f:=(MulAut.congr eD).toMonoidHom.comp D.normalizerMonoidHom
  have hk:f.ker=(centralizer (D:Set H)).subgroupOf (normalizer (D:Set H)):=by
    rw [show f=(MulAut.congr eD).toMonoidHom.comp D.normalizerMonoidHom from rfl,
      MonoidHom.ker_comp_of_injective _ _ (MulAut.congr eD).injective,D.normalizerMonoidHom_ker]
  let eq:= (QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivRange f)
  rcases MathieuSourceSetup.alternating_six_normalizer_models c hG hempty e with h|h|h
  · obtain ⟨eB⟩:=h
    exact Or.inl ⟨eq.trans eB⟩
  · obtain ⟨eB⟩:=h
    exact Or.inr (Or.inl ⟨eq.trans eB⟩)
  · obtain ⟨eB⟩:=h
    exact Or.inr (Or.inr ⟨eq.trans eB⟩)
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
