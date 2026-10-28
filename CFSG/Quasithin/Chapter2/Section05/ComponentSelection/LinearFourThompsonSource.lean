module
public import Theory.SpecificGroups.PSL3Even.ThompsonCentralCover
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearFourModuleSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.RankTwoModelNormality
public import Theory.ElementaryAbelian.Quotient
public import Theory.SpecificGroups.PSL3Four.CentralCover.ElementaryParabolic.Projection
/-! # The original exceptional-cover Thompson product
The source marking proves the covering center elementary. I.2.2(3b) therefore
makes every elementary model preimage elementary. Transporting this along the
actual component inclusion supplies the central-cover Thompson theorem, and
the source component--Sylow generation identifies its centralizer factor with
the original two-core. No additional Thompson, center, or lifting premise is
retained.
Source: Aschbacher--Smith 2.5.7, printed pp.554--555. -/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
private noncomputable def centerQuotientCongr {X Y:Type*} [Group X] [Group Y]
    (e:X≃*Y) : (X⧸center X)≃*(Y⧸center Y) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

theorem MathieuSourceSetup.linear_four_thompson_product
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (e:L⧸center L≃*Matrix.PSL3Four.PSL) :
    Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)=
      ((S:Subgroup H)⊓L.subgroupOf H) ⊔
        (Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H) := by
  let K:=L.subgroupOf H
  let eK:K≃*L:=subgroupOfEquivOfLe c.component_le
  let eQ:K⧸center K≃*Matrix.PSL3Four.PSL:=(centerQuotientCongr eK).trans e
  have hcard : Nat.card Matrix.PSL3Four.F=2^2 := by simpa using Matrix.PSL3Four.card_F
  let := MathieuSourceSetup.linear_nonbinary_component_normal c hG sourceC hempty
    Matrix.PSL3Four.F (by decide : 1<2) hcard e
  let : IsQuasisimple K:=c.component.2
  have hZL:IsPGroup 2 (center L) := by
    rw [MathieuSourceSetup.center_eq_twoCore c hG sourceC hempty]
    exact pCore_isPGroup
  let : Fact (IsPGroup 2 (center L)):=⟨hZL⟩
  let : IsElementaryAbelian 2 (center L):=
    (frattini_eq_bot_iff_isElementaryAbelian (p:=2)).mp
      (MathieuSourceSetup.linear_four_center_frattini c hG sourceC hempty e)
  have hZK:IsPGroup 2 (center K):=hZL.of_equiv (centerCongr eK).symm
  let : IsElementaryAbelian 2 (center K):=IsElementaryAbelian.of_surjective
    (centerCongr eK).symm.toMonoidHom (centerCongr eK).symm.surjective
  have hq (k:K) : Matrix.PSL3Even.ThompsonCentralCover.projection K eQ k=
      Matrix.PSL3Four.ElementaryParabolic.centerProjection e (eK k) := by
    rw [Matrix.PSL3Even.ThompsonCentralCover.projection_apply,
      Matrix.PSL3Four.ElementaryParabolic.centerProjection_apply]
    rfl
  have hlift (W:Subgroup Matrix.PSL3Four.PSL) (hw:IsElementaryAbelian 2 W) :
      IsElementaryAbelian 2 (W.comap (Matrix.PSL3Even.ThompsonCentralCover.projection K eQ)) := by
    let :=hw
    let q:=Matrix.PSL3Even.ThompsonCentralCover.projection K eQ
    let qL:=Matrix.PSL3Four.ElementaryParabolic.centerProjection e
    let : IsElementaryAbelian 2 (W.comap qL):=
      MathieuSourceSetup.linear_four_elementary_preimage c hG sourceC hempty e W
    have hm : (W.comap q).map eK.toMonoidHom=W.comap qL := by
      ext l
      constructor
      · rintro ⟨k,hk,rfl⟩
        change qL (eK k)∈W
        rw [←hq]
        exact hk
      · intro hl
        refine ⟨eK.symm l,?_,eK.apply_symm_apply l⟩
        change q (eK.symm l)∈W
        rw [hq,eK.apply_symm_apply]
        exact hl
    let ew:=((W.comap q).equivMapOfInjective eK.toMonoidHom eK.injective).trans
      (MulEquiv.subgroupCongr hm)
    exact IsElementaryAbelian.of_surjective ew.symm.toMonoidHom ew.symm.surjective
  have he:=Matrix.PSL3Even.ThompsonCentralCover.thompson_eq_sylow_component_sup_centralizer
    K eQ hZK hlift (by decide : 1<2) hcard S
  have hg : K⊔(S:Subgroup H)=⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le c.component_le,←hgen]
    rw [←MonoidHom.range_eq_map,H.range_subtype]
  have ho : componentOrbit K (S:Subgroup H)=K :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      (by rw [normalizer_eq_top]; exact le_top)) (le_componentOrbit _ _)
  have hc := c.component.sylow_centralizer_orbit_eq_pCore S hg
  rw [ho] at hc
  have hJS : Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)≤(S:Subgroup H) :=
    sSup_le fun _ hA => hA.1
  have hi : Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)⊓centralizer (K:Set H)=
      Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H := by
    rw [←hc,←inf_assoc,inf_eq_left.mpr hJS]
  rwa [hi] at he
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
