module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ThompsonPairNormalizers
public import Theory.SpecificGroups.SymplecticFour.ThompsonNormalizerGeneration
/-! # The original symplectic core has nontrivial Frattini subgroup
Trivial Frattini would make the core factor of the proved Thompson product
elementary. The original maximum-family argument then puts every maximum
normalizer in M. The actual point and plane radical normalizers generate
Sp₄, so the component itself would lie in M, contrary to the source marking.
All wing, parabolic, kernel and Sylow-alignment inputs are discharged.
Source: Aschbacher--Smith 2.5.7, printed p.555, first contradiction.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
private noncomputable def centerQuotientEquiv {X Y:Type*} [Group X] [Group Y]
    (e:X≃*Y) : (X⧸center X)≃*(Y⧸center Y) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
private theorem symplectic_core_frattini_ne_bot_of_cover
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] [CharP F 2] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (q:L.subgroupOf H→*(Theory.SpecificGroups.SymplecticFour.Sp F)) (hq:Function.Surjective q)
    (hk:IsPGroup 2 q.ker) (hZ:center (L.subgroupOf H)≤q.ker)
    (hlift:∀W:Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F),IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap q))
    (hJ:elementaryAbelianMaxJ (S:Subgroup H)=((S:Subgroup H)⊓L.subgroupOf H)⊔
      (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H))
    (hbound:frattini (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H:Subgroup H)=⊥→
      ∀A∈elementaryAbelianMaxSubgroups ((S:Subgroup H).map H.subtype),normalizer (A:Set G)≤M) :
    frattini (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H:Subgroup H)≠⊥ := by
  intro hphi
  let K:=L.subgroupOf H
  let C:=elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H
  have hCp:IsPGroup 2 C:=(pCore_isPGroup (p:=2) (G:=H)).to_le inf_le_right
  let : Fact (IsPGroup 2 C):=⟨hCp⟩
  let : IsElementaryAbelian 2 C:=(frattini_eq_bot_iff_isElementaryAbelian (p:=2)).mp hphi
  have hg:K⊔(S:Subgroup H)=⊤:=by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le c.component_le,←hgen]
    rw [←MonoidHom.range_eq_map,H.range_subtype]
  have ho:componentOrbit K (S:Subgroup H)=K:=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl
      (by rw [normalizer_eq_top];exact le_top)) (le_componentOrbit _ _)
  have hc:=c.component.sylow_centralizer_orbit_eq_pCore S hg
  rw [ho] at hc
  have hKC:pCore 2 H≤centralizer (K:Set H):=by rw [←hc];exact inf_le_right
  have hC:C≤centralizer (K:Set H):=inf_le_right.trans hKC
  have hker:((S:Subgroup H)⊓K)⊓C≤q.ker.map K.subtype:=by
    rintro x ⟨hx,hc⟩
    refine ⟨⟨x,hx.2⟩,hZ ?_,rfl⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hC hc y y.property)
  have hnorm (A:Subgroup H) (hA:A∈elementaryAbelianMaxSubgroups (S:Subgroup H)) :
      normalizer (A:Set H)≤M.subgroupOf H:=by
    have ha:=(maxFamily_map_injective_iff H.subtype H.subtype_injective (S:Subgroup H) A).mpr hA
    intro a ha'
    exact hbound hphi _ ha ((A.le_normalizer_map H.subtype) (mem_map_of_mem H.subtype ha'))
  have hKM:=Theory.SpecificGroups.SymplecticFour.ThompsonInner.component_le_of_maxFamily_normalizers_of_sylow
    S K C (M.subgroupOf H) q hq hk hn hF hJ hC hker hlift hnorm
  apply (c.localSetup hG structural115Input sourceC).outside
  intro l hl
  exact hKM (show (⟨l,c.component_le hl⟩:H)∈K from hl)

theorem MathieuSourceSetup.symplectic_thompson_core_frattini_ne_bot
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*(Theory.SpecificGroups.SymplecticFour.Sp F)) :
    frattini (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H:Subgroup H)≠⊥ := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let K:=L.subgroupOf H
  let eK:K≃*(Theory.SpecificGroups.SymplecticFour.Sp F):=(subgroupOfEquivOfLe c.component_le).trans e
  let : K.Normal:=MathieuSourceSetup.symplectic_component_normal c hG sourceC hempty F hF
    (centerQuotientEquiv e)
  have hk:IsPGroup 2 eK.toMonoidHom.ker:=by
    rw [(MonoidHom.ker_eq_bot_iff eK.toMonoidHom).mpr eK.injective]
    exact IsPGroup.of_subsingleton 2 _
  have hZ:center K≤eK.toMonoidHom.ker:=by
    have hZ':center (Theory.SpecificGroups.SymplecticFour.Sp F)=⊥:=
      Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot
    intro k hk
    have he:eK k∈center (Theory.SpecificGroups.SymplecticFour.Sp F):=(centerCongr eK ⟨k,hk⟩).property
    rwa [hZ',mem_bot] at he
  have hlift (W:Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) (hW:IsElementaryAbelian 2 W):
      IsElementaryAbelian 2 (W.comap eK.toMonoidHom):=by
    rw [comap_equiv_eq_map_symm']
    let :=hW
    exact IsElementaryAbelian.map _
  exact symplectic_core_frattini_ne_bot_of_cover c hG sourceC hgen F (by omega) hF
    eK.toMonoidHom eK.surjective hk hZ hlift
    (MathieuSourceSetup.symplectic_thompson_product c hG sourceC hempty hgen F hn hF e)
    (MathieuSourceSetup.symplectic_maxFamily_normalizers_le_of_frattini_eq_bot c hG sourceC hempty hgen F hn hF e)

/-- The literal derived symplectic carrier in the source model list. -/
theorem MathieuSourceSetup.derived_symplectic_thompson_core_frattini_ne_bot
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F)) :
    frattini (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H:Subgroup H)≠⊥ := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  exact MathieuSourceSetup.symplectic_thompson_core_frattini_ne_bot c hG sourceC hempty hgen F hn hF
    (e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn))

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
