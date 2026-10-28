module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ThompsonMarkSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingPreparationKnownSimple
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.CrossingPlanes
public import Theory.GroupTheory.TwoPlaneCover.Ambient
/-! # Original linear crossing-plane commutation
The component Sylow mark extends through the proved Thompson product.
Its kernel is exactly R∩O₂(H); the original disjoint-core and nontrivial
Frattini facts discharge the crossing argument for both root planes.
The simple and central PSL₃(4) source wrappers have no extra local input.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
theorem MathieuSourceSetup.linear_crossing_planes_of_cover
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hJ:elementaryAbelianMaxJ (S:Subgroup H)=((S:Subgroup H)⊓L.subgroupOf H)⊔
      (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H))
    (hphi:frattini (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H:Subgroup G)≠⊥)
    (hc:_root_.commutator (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))≤
      center (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)))
    (F:Type*) [Field F] [Finite F] [CharP F 2] {n:ℕ} (hn:0<n) (hF:Nat.card F=2^n)
    (α:L→*PSL(3,F)) (hα:Function.Surjective α) (hk:α.ker=center L)
    (hlift:∀W:Subgroup PSL(3,F),IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap α))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    let R:=elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)
    let A:=(((S:Subgroup H).map H.subtype)⊓L).subgroupOf R
    ∃f:R→*Matrix.PSL3Even.UnipotentGeometry.U F,
      Function.Surjective (f.comp A.subtype) ∧ f.ker=(R⊓twoCore H).subgroupOf R ∧
      (∀W:Subgroup (Matrix.PSL3Even.UnipotentGeometry.U F),IsElementaryAbelian 2 W→
        IsElementaryAbelian 2 (W.comap (f.comp A.subtype))) ∧
      ∀P:Subgroup (Matrix.PSL3Even.UnipotentGeometry.U F),
        P=Matrix.PSL3Even.UnipotentGeometry.V₁ F∨P=Matrix.PSL3Even.UnipotentGeometry.V₂ F→
        let V:=((P.comap (f.comp A.subtype)).map A.subtype).map R.subtype
        V.conjBy x⁻¹≤centralizer (V:Set G) := by
  let Y:=(S:Subgroup H).map H.subtype
  let R:=elementaryAbelianMaxJ Y
  let A:=(Y⊓L).subgroupOf R
  let C:=R⊓centralizer (L:Set G)
  have hRY:R≤Y:=sSup_le fun _ h=>h.1
  have hcore:=MathieuSourceSetup.core_eq_sylow_centralizer c hgen
  have hC:R⊓twoCore H=C:=by
    rw [hcore,←inf_assoc,inf_eq_left.mpr hRY]
  obtain ⟨f,hf,hk',hKC,hpre⟩:=MathieuSourceSetup.linear_thompson_mark_of_cover c
    (MathieuSourceSetup.ambient_thompson_product c hgen hJ) F hn hF α hα hk hlift
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
  intro P hP
  let :=hpre (Matrix.PSL3Even.UnipotentGeometry.V₁ F) inferInstance
  let :=hpre (Matrix.PSL3Even.UnipotentGeometry.V₂ F) inferInstance
  apply centralizer_conjugate_of_normalizer_action R x⁻¹ hxR
  exact Matrix.PSL3Even.UnipotentGeometry.marked_product_plane_commutes f A P hf hKC hP
    hc hp (R.normalizerMonoidHom ⟨x⁻¹,hxR⟩) hphik hd

theorem MathieuSourceSetup.linear_simple_crossing_planes
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    let R:=elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)
    let A:=(((S:Subgroup H).map H.subtype)⊓L).subgroupOf R
    ∃f:R→*Matrix.PSL3Even.UnipotentGeometry.U F,
      Function.Surjective (f.comp A.subtype) ∧ f.ker=(R⊓twoCore H).subgroupOf R ∧
      (∀W:Subgroup (Matrix.PSL3Even.UnipotentGeometry.U F),IsElementaryAbelian 2 W→
        IsElementaryAbelian 2 (W.comap (f.comp A.subtype))) ∧
      ∀P:Subgroup (Matrix.PSL3Even.UnipotentGeometry.U F),
        P=Matrix.PSL3Even.UnipotentGeometry.V₁ F∨P=Matrix.PSL3Even.UnipotentGeometry.V₂ F→
        let V:=((P.comap (f.comp A.subtype)).map A.subtype).map R.subtype
        V.conjBy x⁻¹≤centralizer (V:Set G) := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let :=MathieuSourceSetup.linear_nonbinary_component_normal c hG localC129Input_knownSimple hempty
    F hn hF (quotientOfLinear F e)
  have prep:=MathieuSourceSetup.linear_simple_crossing_preparation_knownSimple c hG hempty
    hgen F hn hF e x hxT hxS hxN hx2
  have hker:e.toMonoidHom.ker=center L:=by
    have hY:center PSL(3,F)=⊥:=by
      let :=Atlas.sl_perfect (F:=F) 3 (by decide)
      exact Group.IsPerfect.center_quotient_center_eq_bot (SL(3,F))
    rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]
    apply (bot_unique ?_).symm
    intro a ha
    have hh:e a∈center PSL(3,F):=(centerCongr e ⟨a,ha⟩).property
    rw [hY,mem_bot] at hh
    exact e.injective (hh.trans e.map_one.symm)
  apply MathieuSourceSetup.linear_crossing_planes_of_cover c hgen
    (MathieuSourceSetup.linear_simple_thompson_product c hG localC129Input_knownSimple hempty hgen F hn hF e)
    prep.1 prep.2.1 F (by omega) hF e.toMonoidHom e.surjective hker
    (fun W hW=>?_) x hxT hxS hxN hx2
  let :=hW
  exact IsElementaryAbelian.comap_of_injective e.toMonoidHom e.injective W

theorem MathieuSourceSetup.linear_four_crossing_planes
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (e:L⧸center L≃*Matrix.PSL3Four.PSL)
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    let R:=elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)
    let A:=(((S:Subgroup H).map H.subtype)⊓L).subgroupOf R
    ∃f:R→*Matrix.PSL3Even.UnipotentGeometry.U Matrix.PSL3Four.F,
      Function.Surjective (f.comp A.subtype) ∧ f.ker=(R⊓twoCore H).subgroupOf R ∧
      (∀W:Subgroup (Matrix.PSL3Even.UnipotentGeometry.U Matrix.PSL3Four.F),IsElementaryAbelian 2 W→
        IsElementaryAbelian 2 (W.comap (f.comp A.subtype))) ∧
      ∀P:Subgroup (Matrix.PSL3Even.UnipotentGeometry.U Matrix.PSL3Four.F),
        P=Matrix.PSL3Even.UnipotentGeometry.V₁ Matrix.PSL3Four.F∨P=Matrix.PSL3Even.UnipotentGeometry.V₂ Matrix.PSL3Four.F→
        let V:=((P.comap (f.comp A.subtype)).map A.subtype).map R.subtype
        V.conjBy x⁻¹≤centralizer (V:Set G) := by
  let :=MathieuSourceSetup.linear_nonbinary_component_normal c hG localC129Input_knownSimple hempty
    Matrix.PSL3Four.F (by decide : 1<2) (by simpa using Matrix.PSL3Four.card_F) e
  have prep:=MathieuSourceSetup.linear_four_crossing_preparation_knownSimple c hG hempty
    hgen e x hxT hxS hxN hx2
  exact MathieuSourceSetup.linear_crossing_planes_of_cover c hgen
    (MathieuSourceSetup.linear_four_thompson_product c hG localC129Input_knownSimple hempty hgen e)
    prep.1 prep.2.1 Matrix.PSL3Four.F (by decide : 0<2) (by simpa using Matrix.PSL3Four.card_F)
    (Matrix.PSL3Four.ElementaryParabolic.centerProjection e)
    (Matrix.PSL3Four.ElementaryParabolic.centerProjection_surjective e)
    (Matrix.PSL3Four.ElementaryParabolic.centerProjection_ker e)
    (fun W hW=>by
      let :=hW
      exact MathieuSourceSetup.linear_four_elementary_preimage c hG localC129Input_knownSimple hempty e W)
    x hxT hxS hxN hx2
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
