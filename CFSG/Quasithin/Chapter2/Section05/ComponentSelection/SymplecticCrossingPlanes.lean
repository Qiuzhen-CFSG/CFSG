module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ComponentSylowMark
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingPreparationKnownSimple
public import Theory.GroupTheory.CentralProductProjection.Elementary
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.CrossingPlanes
public import Theory.GroupTheory.TwoPlaneCover.Ambient
/-! # Original symplectic crossing-plane commutation
Sylow conjugacy marks the original component intersection. The marked
Thompson quotient has kernel exactly R∩O₂(H), and its elementary wings
commute with their original ambient crossing conjugates. All core,
Frattini, row and C.1.29 inputs are discharged in the derived-model wrapper.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
theorem MathieuSourceSetup.symplectic_thompson_mark_of_equiv
    (c:MathieuSourceSetup H L M S z)
    (hJ:elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)=
      (((S:Subgroup H).map H.subtype)⊓L)⊔
        (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓centralizer (L:Set G)))
    (F:Type*) [Field F] [Finite F] [CharP F 2] {n:ℕ} (hn:0<n) (hF:Nat.card F=2^n)
    (e:L≃*Theory.SpecificGroups.SymplecticFour.Sp F) :
    let R:=elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)
    let A:=(((S:Subgroup H).map H.subtype)⊓L).subgroupOf R
    ∃f:R→*Theory.SpecificGroups.SymplecticFour.unipotent (F:=F),
      Function.Surjective (f.comp A.subtype) ∧
      f.ker=(R⊓centralizer (L:Set G)).subgroupOf R ∧ A≤centralizer (f.ker:Set R) ∧
      ∀W:Subgroup (Theory.SpecificGroups.SymplecticFour.unipotent (F:=F)),IsElementaryAbelian 2 W→
        IsElementaryAbelian 2 (W.comap (f.comp A.subtype)) := by
  let Y:=(S:Subgroup H).map H.subtype
  let R:=elementaryAbelianMaxJ Y
  let A:=Y⊓L
  let C:=R⊓centralizer (L:Set G)
  have hR:R=A⊔C:=hJ
  obtain ⟨P,hP⟩:=MathieuSourceSetup.exists_relative_component_sylow c
  let eA:A≃*P:={
    toFun k:=⟨⟨k,k.property.2⟩,by rw [hP];exact k.property.1⟩
    invFun k:=⟨k.val.val,by
      have hy:(k:L)∈Y.subgroupOf L:=hP ▸ k.property
      exact ⟨hy,k.val.property⟩⟩
    left_inv _:=rfl
    right_inv _:=rfl
    map_mul' _ _:=rfl }
  let Q:=P.mapSurjective (f:=e.toMonoidHom) e.surjective
  let eP:P≃*Theory.SpecificGroups.SymplecticFour.unipotent (F:=F):=
    ((P:Subgroup L).equivMapOfInjective e.toMonoidHom e.injective).trans
      (Sylow.equiv Q (Theory.SpecificGroups.SymplecticFour.unipotentSylow hF hn))
  let q:=eA.trans eP
  have hCbot:C.subgroupOf A=⊥:=by
    apply bot_unique
    intro a ha
    let l:L:=⟨a,a.property.2⟩
    have hz:l∈center L:=by
      apply mem_center_iff.mpr
      intro b
      exact Subtype.ext (ha.2 b b.property)
    have he:e l∈center (Theory.SpecificGroups.SymplecticFour.Sp F):=(centerCongr e ⟨l,hz⟩).property
    rw [Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot,mem_bot] at he
    exact Subtype.ext (show (a:G)=1 from congrArg (fun y:L=>(y:G)) (e.injective (he.trans e.map_one.symm)))
  have hq:q.toMonoidHom.ker=C.subgroupOf A:=by
    rw [(MonoidHom.ker_eq_bot_iff q.toMonoidHom).mpr q.injective,hCbot]
  have hc:A≤centralizer (C:Set G):=
    le_centralizer_iff.mp (inf_le_right.trans (centralizer_le (show A≤L from inf_le_right)))
  apply exists_elementary_relative_projection A C R hc hR q.toMonoidHom hq q.surjective
  intro W hW
  let :=hW
  exact IsElementaryAbelian.comap_of_injective q.toMonoidHom q.injective _

theorem MathieuSourceSetup.symplectic_crossing_planes_of_equiv
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hJ:elementaryAbelianMaxJ (S:Subgroup H)=((S:Subgroup H)⊓L.subgroupOf H)⊔
      (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H))
    (hphi:frattini (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H:Subgroup G)≠⊥)
    (hc:_root_.commutator (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))≤
      center (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)))
    (F:Type*) [Field F] [Finite F] [CharP F 2] {n:ℕ} (hn:0<n) (hF:Nat.card F=2^n)
    (e:L≃*Theory.SpecificGroups.SymplecticFour.Sp F)
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    let R:=elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)
    let A:=(((S:Subgroup H).map H.subtype)⊓L).subgroupOf R
    ∃f:R→*Theory.SpecificGroups.SymplecticFour.unipotent (F:=F),
      Function.Surjective (f.comp A.subtype) ∧ f.ker=(R⊓twoCore H).subgroupOf R ∧
      (∀W:Subgroup (Theory.SpecificGroups.SymplecticFour.unipotent (F:=F)),IsElementaryAbelian 2 W→
        IsElementaryAbelian 2 (W.comap (f.comp A.subtype))) ∧
      ∀i:Bool,
        let V:=(((Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing (F:=F) i).comap (f.comp A.subtype)).map A.subtype).map R.subtype
        V.conjBy x⁻¹≤centralizer (V:Set G) := by
  let Y:=(S:Subgroup H).map H.subtype
  let R:=elementaryAbelianMaxJ Y
  let A:=(Y⊓L).subgroupOf R
  let C:=R⊓centralizer (L:Set G)
  have hRY:R≤Y:=sSup_le fun _ h=>h.1
  have hcore:=MathieuSourceSetup.core_eq_sylow_centralizer c hgen
  have hC:R⊓twoCore H=C:=by
    rw [hcore,←inf_assoc,inf_eq_left.mpr hRY]
  obtain ⟨f,hf,hk',hKC,hpre⟩:=MathieuSourceSetup.symplectic_thompson_mark_of_equiv c
    (MathieuSourceSetup.ambient_thompson_product c hgen hJ) F hn hF e
  have hker:f.ker=(R⊓twoCore H).subgroupOf R:=by rw [hC];exact hk'
  have hphik:frattini f.ker≠⊥:=by
    rw [hker]
    exact frattini_subgroupOf_ne_bot inf_le_left hphi
  have hxR:x⁻¹∈normalizer (R:Set G):=by
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hxY:Y.map (MulAut.conj x⁻¹).toMonoidHom=Y:=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (Y:Set G)).inv_mem hxN)
    change R.map (MulAut.conj x⁻¹).toMonoidHom=R
    rw [←elementaryAbelianMaxJ_map_injective _ (MulAut.conj x⁻¹).injective,hxY]
  have hdcore:Disjoint (twoCore H) ((twoCore H).conjBy x⁻¹):=
    (generated_twoCore_disjoint S (MathieuSourceSetup.sourceTuple c) ⟨c.component_le,c.component⟩ hgen hxT hxS hxN hx2).1
  have hCC:C≤twoCore H:=by rw [←hC];exact inf_le_right
  have hdC:Disjoint C (C.conjBy x⁻¹):=hdcore.mono hCC (map_mono hCC)
  have hd:Disjoint f.ker (f.ker.map (R.normalizerMonoidHom ⟨x⁻¹,hxR⟩).toMonoidHom):=by
    rw [hk']
    exact disjoint_normalizer_image x⁻¹ hxR hdC
  have hp:IsPGroup 2 R:=(S.isPGroup'.map H.subtype).to_le hRY
  refine ⟨f,hf,hker,hpre,?_⟩
  intro i
  let :=hpre (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing (F:=F) false) (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing_elementary _)
  let :=hpre (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing (F:=F) true) (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing_elementary _)
  apply centralizer_conjugate_of_normalizer_action R x⁻¹ hxR
  exact Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.marked_product_wing_commutes f A i hf hKC
    hc hp (R.normalizerMonoidHom ⟨x⁻¹,hxR⟩) hphik hd

private noncomputable def centerQuotientCongr {X Y:Type*} [Group X] [Group Y]
    (e:X≃*Y) : (X⧸center X)≃*(Y⧸center Y) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
theorem MathieuSourceSetup.derived_symplectic_crossing_planes
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    letI : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let R:=elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)
    let A:=(((S:Subgroup H).map H.subtype)⊓L).subgroupOf R
    ∃f:R→*Theory.SpecificGroups.SymplecticFour.unipotent (F:=F),
      Function.Surjective (f.comp A.subtype) ∧ f.ker=(R⊓twoCore H).subgroupOf R ∧
      (∀W:Subgroup (Theory.SpecificGroups.SymplecticFour.unipotent (F:=F)),IsElementaryAbelian 2 W→
        IsElementaryAbelian 2 (W.comap (f.comp A.subtype))) ∧
      ∀i:Bool,
        let V:=(((Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing (F:=F) i).comap (f.comp A.subtype)).map A.subtype).map R.subtype
        V.conjBy x⁻¹≤centralizer (V:Set G) := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let eFull:=e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn)
  let :=MathieuSourceSetup.symplectic_component_normal c hG localC129Input_knownSimple hempty
    F hF (centerQuotientCongr eFull)
  have prep:=MathieuSourceSetup.derived_symplectic_crossing_preparation_knownSimple c hG hempty
    hgen F hn hF e x hxT hxS hxN hx2
  exact MathieuSourceSetup.symplectic_crossing_planes_of_equiv c hgen
    (MathieuSourceSetup.derived_symplectic_thompson_product c hG localC129Input_knownSimple hempty hgen F hn hF e)
    prep.1 prep.2.1 F (by omega) hF eFull x hxT hxS hxN hx2
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
