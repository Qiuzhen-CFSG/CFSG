module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearThompsonSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SymplecticThompsonSource
public import Theory.SpecificGroups.Classical.EvenRankTwoMaxPair
/-! # The two elementary maxima under the source Frattini assumption
For the centerless linear and symplectic branches, the original Thompson
formula is a direct product of the component Sylow and its core intersection.
If the latter has trivial Frattini subgroup, it is elementary. The two actual
root planes or wings therefore give exactly two distinct maximum elementary
subgroups of S. This is the temporary branch used in the normalizer argument;
the subsequent contradiction to empty Gamma-even remains a separate step.
Source: Aschbacher--Smith 2.5.7, printed p.555.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
omit [Finite G] in
private theorem disjoint_component_centralizer {X:Type*} [Group X]
    (K:Subgroup H) (e:K≃*X) (hZ:center X=⊥)
    (C:Subgroup H) (hC:C≤centralizer (K:Set H)) : Disjoint K C := by
  apply disjoint_iff.mpr
  apply bot_unique
  rintro x ⟨hxK,hxC⟩
  have hxZ : (⟨x,hxK⟩:K)∈center K:=by
    apply mem_center_iff.mpr
    intro k
    apply Subtype.ext
    exact hC hxC k k.property
  have he : e ⟨x,hxK⟩∈center X := (centerCongr e ⟨_,hxZ⟩).property
  rw [hZ,mem_bot] at he
  exact congrArg (fun k:K=>(k:H)) (e.injective (he.trans e.map_one.symm))

private theorem core_centralizes_component
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hgen:H=L⊔(S:Subgroup H).map H.subtype) :
    pCore 2 H≤centralizer (L.subgroupOf H:Set H) := by
  have hg : L.subgroupOf H⊔(S:Subgroup H)=⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le c.component_le,←hgen]
    rw [←MonoidHom.range_eq_map,H.range_subtype]
  have ho : componentOrbit (L.subgroupOf H) (S:Subgroup H)=L.subgroupOf H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      (by rw [normalizer_eq_top]; exact le_top)) (le_componentOrbit _ _)
  have hc:=c.component.sylow_centralizer_orbit_eq_pCore S hg
  rw [ho] at hc
  rw [←hc]
  exact inf_le_right

theorem MathieuSourceSetup.linear_simple_maxFamily_pair_of_frattini_eq_bot
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F))
    (hphi:frattini (Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H:Subgroup H)=⊥) :
    ∃ V W:Subgroup H, V≠W ∧ Stellmacher.elementaryAbelianMaxSubgroups (S:Subgroup H)={V,W} := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let K:=L.subgroupOf H
  let eK:K≃*PSL(3,F):=(subgroupOfEquivOfLe c.component_le).trans e
  let SK:=(S:Subgroup H)⊓K
  let C:=Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H
  let : K.Normal:=MathieuSourceSetup.linear_nonbinary_component_normal c hG sourceC hempty F hn hF
    (quotientOfLinear F e)
  have hp:IsPGroup 2 C:=(pCore_isPGroup (p:=2) (G:=H)).to_le inf_le_right
  let : Fact (IsPGroup 2 C):=⟨hp⟩
  let : IsElementaryAbelian 2 C:=(frattini_eq_bot_iff_isElementaryAbelian (p:=2)).mp hphi
  have hcC:C≤centralizer (K:Set H):=inf_le_right.trans (core_centralizes_component c hgen)
  have hZ:center PSL(3,F)=⊥:=by
    let := Atlas.sl_perfect (F:=F) 3 (by decide)
    exact Group.IsPerfect.center_quotient_center_eq_bot (SL(3,F))
  have hd:Disjoint SK C:=(disjoint_component_centralizer K eK hZ C hcC).mono_left inf_le_right
  have hc:SK≤centralizer (C:Set H):=inf_le_right.trans (le_centralizer_iff.mp hcC)
  obtain ⟨R,hR⟩:=S.exists_subgroupOf_eq_of_normal K
  let P:=R.mapSurjective (f:=eK.toMonoidHom) eK.surjective
  have hrmap:(R:Subgroup K).map K.subtype=SK:=by rw [hR,subgroupOf_map_subtype]
  let eU:Matrix.PSL3Even.UnipotentGeometry.U F≃*SK:=
    (((Matrix.PSL3.LinearThree.unipotentEquiv F).trans
      (Sylow.equiv (Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF) P)).trans
      ((R:Subgroup K).equivMapOfInjective eK.toMonoidHom eK.injective).symm).trans
      (((R:Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans
        (MulEquiv.subgroupCongr hrmap))
  have hJ:=MathieuSourceSetup.linear_simple_thompson_product c hG sourceC hempty hgen F hn hF e
  obtain ⟨hpair,hne⟩:=Stellmacher.maxFamily_pair_thompson_equiv (S:Subgroup H) SK C eU
    (Matrix.PSL3Even.UnipotentGeometry.V₁ F) (Matrix.PSL3Even.UnipotentGeometry.V₂ F)
    hJ hd hc (Matrix.PSL3Even.UnipotentGeometry.maxFamily_eq_planes F)
    (fun he=>Matrix.PSL3Even.UnipotentGeometry.plane₁_not_le_plane₂ F he.le)
  exact ⟨_,_,hne,hpair⟩
theorem MathieuSourceSetup.symplectic_maxFamily_pair_of_frattini_eq_bot
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*Theory.SpecificGroups.SymplecticFour.Sp F)
    (hphi:frattini (Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H:Subgroup H)=⊥) :
    ∃ V W:Subgroup H, V≠W ∧ Stellmacher.elementaryAbelianMaxSubgroups (S:Subgroup H)={V,W} := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let K:=L.subgroupOf H
  let eK:K≃*Theory.SpecificGroups.SymplecticFour.Sp F:=(subgroupOfEquivOfLe c.component_le).trans e
  let SK:=(S:Subgroup H)⊓K
  let C:=Stellmacher.elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H
  let eq: L⧸center L≃*ClassicalGroup.PSp 2 F:=QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
  let : K.Normal:=MathieuSourceSetup.symplectic_component_normal c hG sourceC hempty F hF eq
  have hp:IsPGroup 2 C:=(pCore_isPGroup (p:=2) (G:=H)).to_le inf_le_right
  let : Fact (IsPGroup 2 C):=⟨hp⟩
  let : IsElementaryAbelian 2 C:=(frattini_eq_bot_iff_isElementaryAbelian (p:=2)).mp hphi
  have hcC:C≤centralizer (K:Set H):=inf_le_right.trans (core_centralizes_component c hgen)
  have hZ:center (Theory.SpecificGroups.SymplecticFour.Sp F)=⊥:=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot
  have hd:Disjoint SK C:=(disjoint_component_centralizer K eK hZ C hcC).mono_left inf_le_right
  have hc:SK≤centralizer (C:Set H):=inf_le_right.trans (le_centralizer_iff.mp hcC)
  obtain ⟨R,hR⟩:=S.exists_subgroupOf_eq_of_normal K
  let P:=R.mapSurjective (f:=eK.toMonoidHom) eK.surjective
  have hrmap:(R:Subgroup K).map K.subtype=SK:=by rw [hR,subgroupOf_map_subtype]
  let eU:Theory.SpecificGroups.SymplecticFour.unipotent (F:=F)≃*SK:=
    ((Sylow.equiv (Theory.SpecificGroups.SymplecticFour.unipotentSylow hF (by omega)) P).trans
      ((R:Subgroup K).equivMapOfInjective eK.toMonoidHom eK.injective).symm).trans
      (((R:Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans
        (MulEquiv.subgroupCongr hrmap))
  have hJ:=MathieuSourceSetup.symplectic_thompson_product c hG sourceC hempty hgen F hn hF e
  obtain ⟨hpair,hne⟩:=Stellmacher.maxFamily_pair_thompson_equiv (S:Subgroup H) SK C eU
    (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing false)
    (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing true)
    hJ hd hc (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.maxFamily_eq_wings (F:=F))
    (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wings_ne (F:=F))
  exact ⟨_,_,hne,hpair⟩
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
