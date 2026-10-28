module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.AllComponentPlanes
public import Stellmacher.ElementaryAbelianMaxPair.SquareMoving
/-! # The original displaced derived subgroup lies in the two-core
The square-moving crossing actor interchanges the two maximum planes of the
component Sylow. Both crossing planes commute with the original plane, so
the conjugate component Sylow centralizes the original one. The actual
Thompson quotient then kills its derived subgroup, placing it in R∩O₂(H).
The subgroup is nontrivial and normalized by the original S; these are the
three placement inputs of the subsequent 2.5.6/A.3.18 normalizer argument.
Source: Aschbacher--Smith 2.5.7, printed p.556.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
omit [Finite G] in
private theorem source_component_sylow_normalized
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal] :
    (S:Subgroup H).map H.subtype≤normalizer ((((S:Subgroup H).map H.subtype)⊓L:Subgroup G):Set G) := by
  have hSL:(S:Subgroup H).map H.subtype≤normalizer (L:Set G):=
    (map_subtype_le _).trans ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
  intro s hs
  apply mem_normalizer_iff_map_conj_eq.mpr
  change ((((S:Subgroup H).map H.subtype)⊓L).map (MulAut.conj s).toMonoidHom)=
    ((S:Subgroup H).map H.subtype)⊓L
  have hsY:((S:Subgroup H).map H.subtype).map (MulAut.conj s).toMonoidHom=
      (S:Subgroup H).map H.subtype:=
    mem_normalizer_iff_map_conj_eq.mp (((S:Subgroup H).map H.subtype).le_normalizer hs)
  have hsL:L.map (MulAut.conj s).toMonoidHom=L:=mem_normalizer_iff_map_conj_eq.mp (hSL hs)
  rw [Subgroup.map_inf _ _ _ (MulAut.conj s).injective,hsY,hsL]

private theorem source_crossing_derived_core_of_mark
    {Q:Type*} [Group Q]
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hKR:((S:Subgroup H).map H.subtype)⊓L≤elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))
    (f:elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)→*Q)
    (hf:Function.Surjective (f.comp ((((S:Subgroup H).map H.subtype)⊓L).subgroupOf
      (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))).subtype))
    (hk:f.ker=(elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H).subgroupOf
      (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)))
    (P₀ P₁:Subgroup Q)
    (hpre:∀P:Subgroup Q,IsElementaryAbelian 2 P→IsElementaryAbelian 2 (P.comap
      (f.comp ((((S:Subgroup H).map H.subtype)⊓L).subgroupOf
        (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))).subtype)))
    [IsElementaryAbelian 2 P₀] [IsElementaryAbelian 2 P₁]
    (hcard:Nat.card P₀=Nat.card P₁) (hne:P₀≠P₁)
    (hcover:∀A:Subgroup Q,IsElementaryAbelian 2 A→A≤P₀∨A≤P₁)
    (hgen:P₀⊔P₁=⊤) (hQ:_root_.commutator Q≠⊥)
    (V:Subgroup G) (hV:V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L))
    (x:G) (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) (hmove:x^2∉normalizer (V:Set G))
    (hplus:V.conjBy x≤centralizer (V:Set G))
    (hminus:V.conjBy x⁻¹≤centralizer (V:Set G)) :
    let D:=⁅((S:Subgroup H).map H.subtype)⊓L,((S:Subgroup H).map H.subtype)⊓L⁆
    D.conjBy x⁻¹≠⊥ ∧
      D.conjBy x⁻¹≤elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H ∧
      (S:Subgroup H).map H.subtype≤normalizer (D.conjBy x⁻¹:Set G) := by
  let Y:=(S:Subgroup H).map H.subtype
  let R:=elementaryAbelianMaxJ Y
  let K:=Y⊓L
  let A:=K.subgroupOf R
  let q:=f.comp A.subtype
  let i:A→*G:=R.subtype.comp A.subtype
  have hi:Function.Injective i:=R.subtype_injective.comp A.subtype_injective
  have hr:i.range=K:=by
    rw [MonoidHom.range_comp,A.range_subtype,map_subgroupOf_eq_of_le hKR]
  let :=hpre P₀ inferInstance
  let :=hpre P₁ inferInstance
  have hSK:Y≤normalizer (K:Set G):=source_component_sylow_normalized c
  have hgenK:K=V⊔V.conjBy (x^2):=by
    have hh:=marked_maxFamily_moved_plane_generates q hf i hi P₀ P₁ hcard hne hcover hgen V
    rw [hr] at hh
    exact hh hV (x^2) (hSK hx2) hmove
  have hc:K.conjBy x⁻¹≤centralizer (K:Set G):=
    crossing_pair_centralizes_of_square_generation K V x hgenK (hSK hx2) hplus hminus
  have hxR:x⁻¹∈normalizer (R:Set G):=by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change R.map (MulAut.conj x⁻¹).toMonoidHom=R
    have hY:Y.map (MulAut.conj x⁻¹).toMonoidHom=Y:=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (Y:Set G)).inv_mem hxN)
    rw [←elementaryAbelianMaxJ_map_injective _ (MulAut.conj x⁻¹).injective,hY]
  have hBR:K.conjBy x⁻¹≤R:=by
    have hm:=map_mono (f:=(MulAut.conj x⁻¹).toMonoidHom) hKR
    have hR:R.map (MulAut.conj x⁻¹).toMonoidHom=R:=mem_normalizer_iff_map_conj_eq.mp hxR
    rwa [hR] at hm
  have hd:⁅K,K⁆.conjBy x⁻¹=⁅K.conjBy x⁻¹,K.conjBy x⁻¹⁆:=map_commutator _ _ _
  refine ⟨?_,?_,normalizes_conjugate_commutator Y K x⁻¹ hSK ((normalizer (Y:Set G)).inv_mem hxN)⟩
  · intro he
    have hm:=congrArg (fun B:Subgroup G=>B.conjBy x) he
    rw [conjBy_inv',show (⊥:Subgroup G).conjBy x=⊥ from map_bot _] at hm
    exact marked_commutator_ne_bot R K f hf hQ hm
  · rw [hd]
    have hh:=commutator_le_marked_kernel_of_centralizes R K (K.conjBy x⁻¹) f hf hBR hc
    rw [hk,map_subgroupOf_eq_of_le inf_le_left] at hh
    exact hh

private theorem source_sylow_le_thompson
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hJ:elementaryAbelianMaxJ (S:Subgroup H)=((S:Subgroup H)⊓L.subgroupOf H)⊔
      (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H)) :
    ((S:Subgroup H).map H.subtype)⊓L≤elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype) := by
  rw [MathieuSourceSetup.ambient_thompson_product c hgen hJ]
  exact le_sup_left

private theorem linear_sylow_commutator_ne_bot
    (F:Type*) [Field F] : _root_.commutator (Matrix.PSL3Even.UnipotentGeometry.U F)≠⊥ := by
  intro he
  have hc:=(_root_.commutator_eq_bot_iff_center_eq_top _).mp he
  have ha:(⟨1,0,0⟩:Matrix.PSL3Even.UnipotentGeometry.U F)∈center _:=hc.symm ▸ mem_top _
  rw [←Matrix.PSL3Even.UnipotentGeometry.Z_eq_center] at ha
  simp at ha

private theorem symplectic_sylow_commutator_ne_bot
    (F:Type*) [Field F] [Finite F] [CharP F 2] :
    _root_.commutator (Theory.SpecificGroups.SymplecticFour.unipotent (F:=F))≠⊥ := by
  intro he
  have hc:=(_root_.commutator_eq_bot_iff_center_eq_top _).mp he
  have ha:Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element (1:F) 0 0 0∈center _:=hc.symm ▸ mem_top _
  simp only [Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.mem_center_iff_coordinates,
    one_ne_zero,false_and] at ha

/-- The literal displaced derived subgroup in the linear simple source branch.
The plane and square-moving actor are the original selections on p.556. -/
theorem MathieuSourceSetup.linear_simple_crossing_derived_core
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F))
    (V:Subgroup G) (hV:V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) (hmove:x^2∉normalizer (V:Set G)) :
    let D:=⁅((S:Subgroup H).map H.subtype)⊓L,((S:Subgroup H).map H.subtype)⊓L⁆
    D.conjBy x⁻¹≠⊥ ∧
      D.conjBy x⁻¹≤elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H ∧
      (S:Subgroup H).map H.subtype≤normalizer (D.conjBy x⁻¹:Set G) := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let :=MathieuSourceSetup.linear_nonbinary_component_normal c hG localC129Input_knownSimple hempty
    F hn hF (quotientOfLinear F e)
  have hJ:=MathieuSourceSetup.linear_simple_thompson_product c hG localC129Input_knownSimple hempty hgen F hn hF e
  have hKR:=source_sylow_le_thompson c hgen hJ
  obtain ⟨f,hf,hk,hpre,_⟩:=MathieuSourceSetup.linear_simple_crossing_planes c hG hempty hgen F hn hF e x hxT hxS hxN hx2
  have hminus:=MathieuSourceSetup.linear_simple_component_maxima_crossing c hG hempty hgen F hn hF e x hxT hxS hxN hx2 V hV
  have hxSi:x⁻¹∉(S:Subgroup H).map H.subtype:=by
    intro h
    exact hxS (by simpa only [inv_inv] using ((S:Subgroup H).map H.subtype).inv_mem h)
  have hx2i:(x⁻¹)^2∈(S:Subgroup H).map H.subtype:=by
    rw [inv_pow]
    exact ((S:Subgroup H).map H.subtype).inv_mem hx2
  have hplus:V.conjBy x≤centralizer (V:Set G):=by
    simpa only [inv_inv] using MathieuSourceSetup.linear_simple_component_maxima_crossing c hG hempty hgen F hn hF e
      x⁻¹ (c.T.inv_mem hxT) hxSi ((normalizer _).inv_mem hxN) hx2i V hV
  exact source_crossing_derived_core_of_mark c hKR f hf hk
    (Matrix.PSL3Even.UnipotentGeometry.V₁ F) (Matrix.PSL3Even.UnipotentGeometry.V₂ F) hpre
    ((Matrix.PSL3Even.UnipotentGeometry.card_V₁ F).trans (Matrix.PSL3Even.UnipotentGeometry.card_V₂ F).symm)
    (fun he=>Matrix.PSL3Even.UnipotentGeometry.plane₁_not_le_plane₂ F he.le)
    (fun A hA=>by let :=hA;exact Matrix.PSL3Even.UnipotentGeometry.elementary_le_plane F A)
    Matrix.PSL3Even.UnipotentGeometry.planes_generate (linear_sylow_commutator_ne_bot F)
    V hV x hxN hx2 hmove hplus hminus

/-- The literal displaced derived subgroup in the linear four source branch.
The plane and square-moving actor are the original selections on p.556. -/
theorem MathieuSourceSetup.linear_four_crossing_derived_core
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (e:L⧸center L≃*Matrix.PSL3Four.PSL)
    (V:Subgroup G) (hV:V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) (hmove:x^2∉normalizer (V:Set G)) :
    let D:=⁅((S:Subgroup H).map H.subtype)⊓L,((S:Subgroup H).map H.subtype)⊓L⁆
    D.conjBy x⁻¹≠⊥ ∧
      D.conjBy x⁻¹≤elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H ∧
      (S:Subgroup H).map H.subtype≤normalizer (D.conjBy x⁻¹:Set G) := by
  let :=MathieuSourceSetup.linear_nonbinary_component_normal c hG localC129Input_knownSimple hempty
    Matrix.PSL3Four.F (by decide : 1<2) (by simpa using Matrix.PSL3Four.card_F) e
  have hJ:=MathieuSourceSetup.linear_four_thompson_product c hG localC129Input_knownSimple hempty hgen e
  have hKR:=source_sylow_le_thompson c hgen hJ
  obtain ⟨f,hf,hk,hpre,_⟩:=MathieuSourceSetup.linear_four_crossing_planes c hG hempty hgen e x hxT hxS hxN hx2
  have hminus:=MathieuSourceSetup.linear_four_component_maxima_crossing c hG hempty hgen e x hxT hxS hxN hx2 V hV
  have hxSi:x⁻¹∉(S:Subgroup H).map H.subtype:=by
    intro h
    exact hxS (by simpa only [inv_inv] using ((S:Subgroup H).map H.subtype).inv_mem h)
  have hx2i:(x⁻¹)^2∈(S:Subgroup H).map H.subtype:=by
    rw [inv_pow]
    exact ((S:Subgroup H).map H.subtype).inv_mem hx2
  have hplus:V.conjBy x≤centralizer (V:Set G):=by
    simpa only [inv_inv] using MathieuSourceSetup.linear_four_component_maxima_crossing c hG hempty hgen e
      x⁻¹ (c.T.inv_mem hxT) hxSi ((normalizer _).inv_mem hxN) hx2i V hV
  exact source_crossing_derived_core_of_mark c hKR f hf hk
    (Matrix.PSL3Even.UnipotentGeometry.V₁ Matrix.PSL3Four.F) (Matrix.PSL3Even.UnipotentGeometry.V₂ Matrix.PSL3Four.F) hpre
    ((Matrix.PSL3Even.UnipotentGeometry.card_V₁ Matrix.PSL3Four.F).trans (Matrix.PSL3Even.UnipotentGeometry.card_V₂ Matrix.PSL3Four.F).symm)
    (fun he=>Matrix.PSL3Even.UnipotentGeometry.plane₁_not_le_plane₂ Matrix.PSL3Four.F he.le)
    (fun A hA=>by let :=hA;exact Matrix.PSL3Even.UnipotentGeometry.elementary_le_plane Matrix.PSL3Four.F A)
    Matrix.PSL3Even.UnipotentGeometry.planes_generate (linear_sylow_commutator_ne_bot Matrix.PSL3Four.F)
    V hV x hxN hx2 hmove hplus hminus

/-- The literal displaced derived subgroup in the derived symplectic source branch.
The plane and square-moving actor are the original selections on p.556. -/
theorem MathieuSourceSetup.derived_symplectic_crossing_derived_core
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F))
    (V:Subgroup G) (hV:V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) (hmove:x^2∉normalizer (V:Set G)) :
    let D:=⁅((S:Subgroup H).map H.subtype)⊓L,((S:Subgroup H).map H.subtype)⊓L⁆
    D.conjBy x⁻¹≠⊥ ∧
      D.conjBy x⁻¹≤elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H ∧
      (S:Subgroup H).map H.subtype≤normalizer (D.conjBy x⁻¹:Set G) := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let eFull:=e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn)
  let eq:L⧸center L≃*ClassicalGroup.PSp 2 F:=QuotientGroup.congr _ _ eFull (by
    apply le_antisymm
    · rintro _ ⟨a,ha,rfl⟩
      exact (centerCongr eFull ⟨a,ha⟩).property
    · intro a ha
      exact ⟨eFull.symm a,(centerCongr eFull.symm ⟨a,ha⟩).property,eFull.apply_symm_apply a⟩)
  let :=MathieuSourceSetup.symplectic_component_normal c hG localC129Input_knownSimple hempty F hF eq
  have hJ:=MathieuSourceSetup.derived_symplectic_thompson_product c hG localC129Input_knownSimple hempty hgen F hn hF e
  have hKR:=source_sylow_le_thompson c hgen hJ
  obtain ⟨f,hf,hk,hpre,_⟩:=MathieuSourceSetup.derived_symplectic_crossing_planes c hG hempty hgen F hn hF e x hxT hxS hxN hx2
  have hminus:=MathieuSourceSetup.derived_symplectic_component_maxima_crossing c hG hempty hgen F hn hF e x hxT hxS hxN hx2 V hV
  have hxSi:x⁻¹∉(S:Subgroup H).map H.subtype:=by
    intro h
    exact hxS (by simpa only [inv_inv] using ((S:Subgroup H).map H.subtype).inv_mem h)
  have hx2i:(x⁻¹)^2∈(S:Subgroup H).map H.subtype:=by
    rw [inv_pow]
    exact ((S:Subgroup H).map H.subtype).inv_mem hx2
  have hplus:V.conjBy x≤centralizer (V:Set G):=by
    simpa only [inv_inv] using MathieuSourceSetup.derived_symplectic_component_maxima_crossing c hG hempty hgen F hn hF e
      x⁻¹ (c.T.inv_mem hxT) hxSi ((normalizer _).inv_mem hxN) hx2i V hV
  let :=Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing_elementary (F:=F) false
  let :=Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing_elementary (F:=F) true
  let : Algebra (ZMod 2) F:=ZMod.algebra F 2
  exact source_crossing_derived_core_of_mark c hKR f hf hk
    (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing (F:=F) false)
    (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing (F:=F) true) hpre
    ((Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.card_wing false).trans
      (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.card_wing true).symm)
    Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wings_ne
    (fun A hA=>by let :=hA;exact SymplecticConjugatePair.elementary_le_wing A)
    Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wings_generate (symplectic_sylow_commutator_ne_bot F)
    V hV x hxN hx2 hmove hplus hminus
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
