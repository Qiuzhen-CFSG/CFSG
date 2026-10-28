module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.PlaneNormalizerSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingNormalizerSource
public import Theory.GroupTheory.TwoGroupSquareChoice
/-! # The actual square-moving crossing plane
The original component supplies a maximum plane whose component normalizer
escapes M. Its marked quotient gives the index and centralizer bounds. The
normalizer condition produces an outside element, and the source beta
normalizer contradiction rechooses it so that its square moves the plane.
All witnesses are constructed in each original rank-two source branch.
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

omit [Finite G] in
private theorem crossing_inverse_centralizes (V:Subgroup G) (x:G)
    (h:V.conjBy x⁻¹≤centralizer (V:Set G)) :
    V.conjBy x≤centralizer (V:Set G) := by
  rintro _ ⟨v,hv,rfl⟩ w hw
  have hh:=congrArg (MulAut.conj x) (h (mem_map_of_mem _ hw) v hv)
  simpa [MulAut.conj_apply,mul_assoc] using hh.symm

private theorem source_square_moving_of_mark
    {Q:Type*} [Group Q]
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hJ:elementaryAbelianMaxJ (S:Subgroup H)=((S:Subgroup H)⊓L.subgroupOf H)⊔
      (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H))
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
    (hpgen:P₀⊔P₁=⊤) (hc₀:centralizer (P₀:Set Q)=P₀) (hc₁:centralizer (P₁:Set Q)=P₁)
    (hescape:∃V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L),
      ¬L⊓normalizer (V:Set G)≤M)
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype)
    (hcross:∀V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L),
      V.conjBy x⁻¹≤centralizer (V:Set G)) :
    ∃V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L),
      ∃y:G,y∈c.T ∧ y∉(S:Subgroup H).map H.subtype ∧
      y∈normalizer ((S:Subgroup H).map H.subtype:Set G) ∧
      y^2∈(S:Subgroup H).map H.subtype ∧ y^2∉normalizer (V:Set G) := by
  let Y:=(S:Subgroup H).map H.subtype
  let R:=elementaryAbelianMaxJ Y
  let K:=Y⊓L
  have hRY:R≤Y:=sSup_le fun _ h=>h.1
  have hcore:=MathieuSourceSetup.core_eq_sylow_centralizer c hgen
  have hRC:R⊓twoCore H=R⊓centralizer (L:Set G):=by
    rw [hcore,←inf_assoc,inf_eq_left.mpr hRY]
  have hR:R=K⊔(R⊓twoCore H):=by
    rw [hRC]
    exact MathieuSourceSetup.ambient_thompson_product c hgen hJ
  have hKR:K≤R:=by rw [hR];exact le_sup_left
  have hC:twoCore H≤centralizer (K:Set G):=by
    rw [hcore]
    exact inf_le_right.trans (centralizer_le inf_le_right)
  let :=hpre P₀ inferInstance
  let :=hpre P₁ inferInstance
  have hg:=marked_pair_plane_geometry R K (twoCore H) Y hKR hR
    (source_component_sylow_normalized c) hC f hf hk P₀ P₁ hcard hne hcover hpgen hc₀ hc₁
  obtain ⟨V,hV,hout⟩:=hescape
  obtain ⟨hRV,hCV,hi,hcent⟩:=hg V hV
  refine ⟨V,hV,?_⟩
  exact MathieuSourceSetup.exists_square_moving_crossing_plane c hG hempty hgen
    V (L⊓normalizer (V:Set G)) (hV.1.trans hKR) hRV hCV hi hcent
    (le_inf (hV.1.trans inf_le_right) V.le_normalizer) inf_le_left inf_le_right hout
    x hxT hxS hxN hx2 (crossing_inverse_centralizes V x (hcross V hV))

theorem MathieuSourceSetup.linear_simple_square_moving_plane
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F)) :
    ∃V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L),
      ∃x:G,x∈c.T ∧ x∉(S:Subgroup H).map H.subtype ∧
      x∈normalizer ((S:Subgroup H).map H.subtype:Set G) ∧
      x^2∈(S:Subgroup H).map H.subtype ∧ x^2∉normalizer (V:Set G) := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let :=MathieuSourceSetup.linear_nonbinary_component_normal c hG localC129Input_knownSimple hempty
    F hn hF (quotientOfLinear F e)
  obtain ⟨x,hxT,hxS,hxN,hx2⟩:=exists_outside_normalizer_square_mem
    ((S:Subgroup H).map H.subtype) c.T c.T.isPGroup' c.sylow_lt
  have hJ:=MathieuSourceSetup.linear_simple_thompson_product c hG localC129Input_knownSimple hempty hgen F hn hF e
  obtain ⟨f,hf,hk,hpre,_⟩:=MathieuSourceSetup.linear_simple_crossing_planes c hG hempty hgen F hn hF e x hxT hxS hxN hx2
  apply source_square_moving_of_mark c hG hempty hgen hJ f hf hk
    (Matrix.PSL3Even.UnipotentGeometry.V₁ F) (Matrix.PSL3Even.UnipotentGeometry.V₂ F) hpre
    ((Matrix.PSL3Even.UnipotentGeometry.card_V₁ F).trans (Matrix.PSL3Even.UnipotentGeometry.card_V₂ F).symm)
    (fun he=>Matrix.PSL3Even.UnipotentGeometry.plane₁_not_le_plane₂ F he.le)
    (fun A hA=>by let :=hA;exact Matrix.PSL3Even.UnipotentGeometry.elementary_le_plane F A)
    Matrix.PSL3Even.UnipotentGeometry.planes_generate
    Matrix.PSL3Even.UnipotentGeometry.plane₁_self_centralizer
    Matrix.PSL3Even.UnipotentGeometry.plane₂_self_centralizer
    (MathieuSourceSetup.linear_simple_component_plane_escapes c hG F hn hF e)
    x hxT hxS hxN hx2
  exact MathieuSourceSetup.linear_simple_component_maxima_crossing c hG hempty hgen F hn hF e x hxT hxS hxN hx2

theorem MathieuSourceSetup.linear_four_square_moving_plane
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (e:L⧸center L≃*Matrix.PSL3Four.PSL) :
    ∃V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L),
      ∃x:G,x∈c.T ∧ x∉(S:Subgroup H).map H.subtype ∧
      x∈normalizer ((S:Subgroup H).map H.subtype:Set G) ∧
      x^2∈(S:Subgroup H).map H.subtype ∧ x^2∉normalizer (V:Set G) := by
  let :=MathieuSourceSetup.linear_nonbinary_component_normal c hG localC129Input_knownSimple hempty
    Matrix.PSL3Four.F (by decide : 1<2) (by simpa using Matrix.PSL3Four.card_F) e
  obtain ⟨x,hxT,hxS,hxN,hx2⟩:=exists_outside_normalizer_square_mem
    ((S:Subgroup H).map H.subtype) c.T c.T.isPGroup' c.sylow_lt
  have hJ:=MathieuSourceSetup.linear_four_thompson_product c hG localC129Input_knownSimple hempty hgen e
  obtain ⟨f,hf,hk,hpre,_⟩:=MathieuSourceSetup.linear_four_crossing_planes c hG hempty hgen e x hxT hxS hxN hx2
  apply source_square_moving_of_mark c hG hempty hgen hJ f hf hk
    (Matrix.PSL3Even.UnipotentGeometry.V₁ Matrix.PSL3Four.F) (Matrix.PSL3Even.UnipotentGeometry.V₂ Matrix.PSL3Four.F) hpre
    ((Matrix.PSL3Even.UnipotentGeometry.card_V₁ Matrix.PSL3Four.F).trans (Matrix.PSL3Even.UnipotentGeometry.card_V₂ Matrix.PSL3Four.F).symm)
    (fun he=>Matrix.PSL3Even.UnipotentGeometry.plane₁_not_le_plane₂ Matrix.PSL3Four.F he.le)
    (fun A hA=>by let :=hA;exact Matrix.PSL3Even.UnipotentGeometry.elementary_le_plane Matrix.PSL3Four.F A)
    Matrix.PSL3Even.UnipotentGeometry.planes_generate
    Matrix.PSL3Even.UnipotentGeometry.plane₁_self_centralizer
    Matrix.PSL3Even.UnipotentGeometry.plane₂_self_centralizer
    (MathieuSourceSetup.linear_four_component_plane_escapes c hG hempty e)
    x hxT hxS hxN hx2
  exact MathieuSourceSetup.linear_four_component_maxima_crossing c hG hempty hgen e x hxT hxS hxN hx2

theorem MathieuSourceSetup.derived_symplectic_square_moving_plane
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F)) :
    ∃V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L),
      ∃x:G,x∈c.T ∧ x∉(S:Subgroup H).map H.subtype ∧
      x∈normalizer ((S:Subgroup H).map H.subtype:Set G) ∧
      x^2∈(S:Subgroup H).map H.subtype ∧ x^2∉normalizer (V:Set G) := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let eFull:=e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn)
  let eq:L⧸center L≃*ClassicalGroup.PSp 2 F:=QuotientGroup.congr _ _ eFull (by
    apply le_antisymm
    · rintro _ ⟨a,ha,rfl⟩
      exact (centerCongr eFull ⟨a,ha⟩).property
    · intro a ha
      exact ⟨eFull.symm a,(centerCongr eFull.symm ⟨a,ha⟩).property,eFull.apply_symm_apply a⟩)
  let :=MathieuSourceSetup.symplectic_component_normal c hG localC129Input_knownSimple hempty F hF eq
  obtain ⟨x,hxT,hxS,hxN,hx2⟩:=exists_outside_normalizer_square_mem
    ((S:Subgroup H).map H.subtype) c.T c.T.isPGroup' c.sylow_lt
  have hJ:=MathieuSourceSetup.derived_symplectic_thompson_product c hG localC129Input_knownSimple hempty hgen F hn hF e
  obtain ⟨f,hf,hk,hpre,_⟩:=MathieuSourceSetup.derived_symplectic_crossing_planes c hG hempty hgen F hn hF e x hxT hxS hxN hx2
  let :=Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing_elementary (F:=F) false
  let :=Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing_elementary (F:=F) true
  let : Algebra (ZMod 2) F:=ZMod.algebra F 2
  apply source_square_moving_of_mark c hG hempty hgen hJ f hf hk
    (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing (F:=F) false)
    (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing (F:=F) true) hpre
    ((Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.card_wing false).trans
      (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.card_wing true).symm)
    Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wings_ne
    (fun A hA=>by let :=hA;exact SymplecticConjugatePair.elementary_le_wing A)
    Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wings_generate
    (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing_self_centralizer false)
    (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing_self_centralizer true)
    (MathieuSourceSetup.derived_symplectic_component_plane_escapes c hG F hn hF e)
    x hxT hxS hxN hx2
  exact MathieuSourceSetup.derived_symplectic_component_maxima_crossing c hG hempty hgen F hn hF e x hxT hxS hxN hx2
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
