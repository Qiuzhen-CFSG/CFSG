module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearCrossingPlanes
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SymplecticCrossingPlanes
public import Stellmacher.ElementaryAbelianMaxPair.MarkedCover
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings
/-! # Every original component maximum plane crosses centrally
The marked elementary preimages are exactly the intrinsic maximum family
of the component Sylow. Thus the crossing result applies to every fixed
source plane, independently of the coordinate mark and chosen actor.
All three original model branches discharge the marked quotient inputs.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
omit [Finite G] in
private theorem source_sylow_le_thompson
    (c:MathieuSourceSetup H L M S z)
    (hJ:elementaryAbelianMaxJ (S:Subgroup H)=((S:Subgroup H)⊓L.subgroupOf H)⊔
      (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H)) :
    ((S:Subgroup H).map H.subtype)⊓L≤elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype) := by
  have hle:(S:Subgroup H)⊓L.subgroupOf H≤elementaryAbelianMaxJ (S:Subgroup H):=by
    rw [hJ]
    exact le_sup_left
  have hm:=map_mono (f:=H.subtype) hle
  rwa [Subgroup.map_inf _ _ _ H.subtype_injective,map_subgroupOf_eq_of_le c.component_le,
    ←elementaryAbelianMaxJ_map_injective _ H.subtype_injective] at hm

private theorem linear_mark_maxima_cross
    {F:Type*} [Field F] [Finite F] [CharP F 2]
    (R K:Subgroup G) (hKR:K≤R) (f:R→*Matrix.PSL3Even.UnipotentGeometry.U F)
    (hf:Function.Surjective (f.comp (K.subgroupOf R).subtype))
    (hpre:∀W:Subgroup (Matrix.PSL3Even.UnipotentGeometry.U F),IsElementaryAbelian 2 W→
      IsElementaryAbelian 2 (W.comap (f.comp (K.subgroupOf R).subtype)))
    (x:G)
    (hcross:∀P:Subgroup (Matrix.PSL3Even.UnipotentGeometry.U F),
      P=Matrix.PSL3Even.UnipotentGeometry.V₁ F∨P=Matrix.PSL3Even.UnipotentGeometry.V₂ F→
      let V:=((P.comap (f.comp (K.subgroupOf R).subtype)).map (K.subgroupOf R).subtype).map R.subtype
      V.conjBy x≤centralizer (V:Set G)) :
    ∀V∈elementaryAbelianMaxSubgroups K,V.conjBy x≤centralizer (V:Set G) := by
  let A:=K.subgroupOf R
  let q:=f.comp A.subtype
  let i:A→*G:=R.subtype.comp A.subtype
  have hi:Function.Injective i:=R.subtype_injective.comp A.subtype_injective
  have hr:i.range=K:=by
    rw [MonoidHom.range_comp,A.range_subtype,map_subgroupOf_eq_of_le hKR]
  let :=hpre (Matrix.PSL3Even.UnipotentGeometry.V₁ F) inferInstance
  let :=hpre (Matrix.PSL3Even.UnipotentGeometry.V₂ F) inferInstance
  have hp:=maxFamily_pair_of_marked_image q hf i hi
    (Matrix.PSL3Even.UnipotentGeometry.V₁ F) (Matrix.PSL3Even.UnipotentGeometry.V₂ F)
    ((Matrix.PSL3Even.UnipotentGeometry.card_V₁ F).trans (Matrix.PSL3Even.UnipotentGeometry.card_V₂ F).symm)
    (fun he=>Matrix.PSL3Even.UnipotentGeometry.plane₁_not_le_plane₂ F he.le)
    (fun D hD=>by let :=hD;exact Matrix.PSL3Even.UnipotentGeometry.elementary_le_plane F D)
  rw [hr] at hp
  intro V hV
  rw [hp.1] at hV
  rcases hV with rfl|rfl
  · simpa only [Subgroup.map_map,i] using hcross (Matrix.PSL3Even.UnipotentGeometry.V₁ F) (Or.inl rfl)
  · simpa only [Subgroup.map_map,i] using hcross (Matrix.PSL3Even.UnipotentGeometry.V₂ F) (Or.inr rfl)

private theorem symplectic_mark_maxima_cross
    {F:Type*} [Field F] [Finite F] [CharP F 2]
    (R K:Subgroup G) (hKR:K≤R) (f:R→*Theory.SpecificGroups.SymplecticFour.unipotent (F:=F))
    (hf:Function.Surjective (f.comp (K.subgroupOf R).subtype))
    (hpre:∀W:Subgroup (Theory.SpecificGroups.SymplecticFour.unipotent (F:=F)),IsElementaryAbelian 2 W→
      IsElementaryAbelian 2 (W.comap (f.comp (K.subgroupOf R).subtype)))
    (x:G)
    (hcross:∀b:Bool,
      let V:=(((Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing (F:=F) b).comap
        (f.comp (K.subgroupOf R).subtype)).map (K.subgroupOf R).subtype).map R.subtype
      V.conjBy x≤centralizer (V:Set G)) :
    ∀V∈elementaryAbelianMaxSubgroups K,V.conjBy x≤centralizer (V:Set G) := by
  let A:=K.subgroupOf R
  let q:=f.comp A.subtype
  let i:A→*G:=R.subtype.comp A.subtype
  have hi:Function.Injective i:=R.subtype_injective.comp A.subtype_injective
  have hr:i.range=K:=by
    rw [MonoidHom.range_comp,A.range_subtype,map_subgroupOf_eq_of_le hKR]
  let : Algebra (ZMod 2) F:=ZMod.algebra F 2
  let :=hpre (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing (F:=F) false)
    (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing_elementary _)
  let :=hpre (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing (F:=F) true)
    (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing_elementary _)
  have hne:Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing (F:=F) false≠
      Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing (F:=F) true:=by
    intro h
    have he:Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element (1:F) 0 0 0∈
        Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing true:=by
      rw [←h]
      exact (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element_mem_wing _ _ _ _ _).mpr rfl
    have hh:(1:F)=0:=by
      simpa only [Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element_mem_wing,↓reduceIte] using he
    exact one_ne_zero hh
  have hp:=maxFamily_pair_of_marked_image q hf i hi
    (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing (F:=F) false)
    (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.wing (F:=F) true)
    ((Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.card_wing false).trans
      (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.card_wing true).symm) hne
    (fun D hD=>by let :=hD;exact SymplecticConjugatePair.elementary_le_wing D)
  rw [hr] at hp
  intro V hV
  rw [hp.1] at hV
  rcases hV with rfl|rfl
  · simpa only [Subgroup.map_map,i] using hcross false
  · simpa only [Subgroup.map_map,i] using hcross true

theorem MathieuSourceSetup.linear_simple_component_maxima_crossing
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    ∀V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L),
      V.conjBy x⁻¹≤centralizer (V:Set G) := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hJ:=MathieuSourceSetup.linear_simple_thompson_product c hG localC129Input_knownSimple hempty hgen F hn hF e
  have hKR:=source_sylow_le_thompson c hJ
  obtain ⟨f,hf,_,hpre,hcross⟩:=MathieuSourceSetup.linear_simple_crossing_planes c hG hempty hgen F hn hF e x hxT hxS hxN hx2
  exact linear_mark_maxima_cross _ _ hKR f hf hpre x⁻¹ hcross

theorem MathieuSourceSetup.linear_four_component_maxima_crossing
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (e:L⧸center L≃*Matrix.PSL3Four.PSL)
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    ∀V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L),
      V.conjBy x⁻¹≤centralizer (V:Set G) := by
  have hJ:=MathieuSourceSetup.linear_four_thompson_product c hG localC129Input_knownSimple hempty hgen e
  have hKR:=source_sylow_le_thompson c hJ
  obtain ⟨f,hf,_,hpre,hcross⟩:=MathieuSourceSetup.linear_four_crossing_planes c hG hempty hgen e x hxT hxS hxN hx2
  exact linear_mark_maxima_cross _ _ hKR f hf hpre x⁻¹ hcross

theorem MathieuSourceSetup.derived_symplectic_component_maxima_crossing
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    ∀V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L),
      V.conjBy x⁻¹≤centralizer (V:Set G) := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hJ:=MathieuSourceSetup.derived_symplectic_thompson_product c hG localC129Input_knownSimple hempty hgen F hn hF e
  have hKR:=source_sylow_le_thompson c hJ
  obtain ⟨f,hf,_,hpre,hcross⟩:=MathieuSourceSetup.derived_symplectic_crossing_planes c hG hempty hgen F hn hF e x hxT hxS hxN hx2
  exact symplectic_mark_maxima_cross _ _ hKR f hf hpre x⁻¹ hcross
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
