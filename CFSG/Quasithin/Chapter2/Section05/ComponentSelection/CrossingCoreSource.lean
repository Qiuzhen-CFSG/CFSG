module
public import Stellmacher.ElementaryAbelianMaxPair.CrossingEmbedding
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearFourThompsonSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearThompsonSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SymplecticThompsonSource
public import CFSG.Quasithin.Chapter2.Section01To03.Selection.Persistence
/-! # The original crossing core embeds in the component Sylow quotient
The source tuple gives disjoint conjugate two-cores. The proved Thompson
products put the crossing core in the commuting product with the component
Sylow subgroup. Projection to the component center quotient is therefore
faithful, with its range in the actual Sylow image. The three final model
applications discharge both normality and the Thompson-product premise.
Source: Aschbacher--Smith 2.5.7, printed p.555, after the first contradiction.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
private noncomputable def centerQuotientCongr {X Y:Type*} [Group X] [Group Y]
    (e:X≃*Y) : (X⧸center X)≃*(Y⧸center Y) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

theorem MathieuSourceSetup.sourceTuple (c:MathieuSourceSetup H L M S z) :
    SourceTuple M H ((S:Subgroup H).map H.subtype) (c.T:Subgroup G) z := by
  refine ⟨c.gamma,?_,?_,c.center_le,c.sylow_lt,c.involution,c.mem_center⟩
  · exact (lemma_2_3_8_1 c.T c.sylow_le c.unique
      (c.gamma.elim (fun h=>h.1.1) (fun h=>h.1)) c.pair S c.base_le).2.2.2
  · exact ⟨c.T.subtype c.sylow_le,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le c.sylow_le]⟩

theorem MathieuSourceSetup.core_eq_sylow_centralizer
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hgen:H=L⊔(S:Subgroup H).map H.subtype) :
    twoCore H=(S:Subgroup H).map H.subtype⊓centralizer (L:Set G) := by
  have hSL:(S:Subgroup H).map H.subtype≤normalizer (L:Set G):=
    (map_subtype_le _).trans ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
  have ho:componentOrbit L ((S:Subgroup H).map H.subtype)=L:=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hSL) (le_componentOrbit _ _)
  have he:=generated_orbit_core ⟨c.component_le,c.component⟩ S hgen
  rw [ho] at he
  exact he.symm

theorem MathieuSourceSetup.ambient_thompson_product
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hJ:elementaryAbelianMaxJ (S:Subgroup H)=((S:Subgroup H)⊓L.subgroupOf H)⊔
      (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H)) :
    elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)=
      (((S:Subgroup H).map H.subtype)⊓L)⊔
        (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓centralizer (L:Set G)) := by
  let Y:=(S:Subgroup H).map H.subtype
  let R:=elementaryAbelianMaxJ Y
  have hRY:R≤Y:=sSup_le fun _ hA=>hA.1
  have hcore:=MathieuSourceSetup.core_eq_sylow_centralizer c hgen
  have hC:R⊓twoCore H=R⊓centralizer (L:Set G):=by
    rw [hcore,←inf_assoc,inf_eq_left.mpr hRY]
  have hm:=congrArg (Subgroup.map H.subtype) hJ
  rw [Subgroup.map_sup,Subgroup.map_inf _ _ _ H.subtype_injective,
    Subgroup.map_inf _ _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le c.component_le,
    ←elementaryAbelianMaxJ_map_injective _ H.subtype_injective] at hm
  change R=(Y⊓L)⊔(R⊓twoCore H) at hm
  rwa [hC] at hm

theorem MathieuSourceSetup.thompson_core_embedding_of_product
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hJ:elementaryAbelianMaxJ (S:Subgroup H)=((S:Subgroup H)⊓L.subgroupOf H)⊔
      (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    ∃j:((elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H).conjBy x⁻¹)→*(L⧸center L),
      Function.Injective j ∧
      j.range≤(((S:Subgroup H).map H.subtype).subgroupOf L).map (QuotientGroup.mk' (center L)) := by
  let Y:=(S:Subgroup H).map H.subtype
  let R:=elementaryAbelianMaxJ Y
  have hRY:R≤Y:=sSup_le fun _ hA=>hA.1
  have hcore:=MathieuSourceSetup.core_eq_sylow_centralizer c hgen
  have hC:R⊓twoCore H=R⊓centralizer (L:Set G):=by
    rw [hcore,←inf_assoc,inf_eq_left.mpr hRY]
  have hm:=MathieuSourceSetup.ambient_thompson_product c hgen hJ
  have hd:Disjoint (Y⊓centralizer (L:Set G)) ((Y⊓centralizer (L:Set G)).conjBy x⁻¹):=by
    rw [←hcore]
    exact (generated_twoCore_disjoint S (MathieuSourceSetup.sourceTuple c) ⟨c.component_le,c.component⟩ hgen hxT hxS hxN hx2).1
  obtain ⟨j,hj,hr⟩:=crossing_thompson_core_embedding Y L hm x⁻¹
    ((normalizer (Y:Set G)).inv_mem hxN) hd
  rw [hC]
  exact ⟨j,hj,hr⟩

theorem MathieuSourceSetup.linear_simple_crossing_core_embedding
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    ∃j:((elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H).conjBy x⁻¹)→*(L⧸center L),
      Function.Injective j ∧
      j.range≤(((S:Subgroup H).map H.subtype).subgroupOf L).map (QuotientGroup.mk' (center L)) := by
  let := MathieuSourceSetup.linear_nonbinary_component_normal c hG sourceC hempty F hn hF
    (quotientOfLinear F e)
  exact MathieuSourceSetup.thompson_core_embedding_of_product c hgen
    (MathieuSourceSetup.linear_simple_thompson_product c hG sourceC hempty hgen F hn hF e) x hxT hxS hxN hx2

theorem MathieuSourceSetup.linear_four_crossing_core_embedding
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (e:L⧸center L≃*Matrix.PSL3Four.PSL)
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    ∃j:((elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H).conjBy x⁻¹)→*(L⧸center L),
      Function.Injective j ∧
      j.range≤(((S:Subgroup H).map H.subtype).subgroupOf L).map (QuotientGroup.mk' (center L)) := by
  let := MathieuSourceSetup.linear_nonbinary_component_normal c hG sourceC hempty
    Matrix.PSL3Four.F (by decide : 1<2) (by simpa using Matrix.PSL3Four.card_F) e
  exact MathieuSourceSetup.thompson_core_embedding_of_product c hgen
    (MathieuSourceSetup.linear_four_thompson_product c hG sourceC hempty hgen e) x hxT hxS hxN hx2

theorem MathieuSourceSetup.derived_symplectic_crossing_core_embedding
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    ∃j:((elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H).conjBy x⁻¹)→*(L⧸center L),
      Function.Injective j ∧
      j.range≤(((S:Subgroup H).map H.subtype).subgroupOf L).map (QuotientGroup.mk' (center L)) := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let eFull:=e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn)
  let := MathieuSourceSetup.symplectic_component_normal c hG sourceC hempty F hF
    (centerQuotientCongr eFull)
  exact MathieuSourceSetup.thompson_core_embedding_of_product c hgen
    (MathieuSourceSetup.derived_symplectic_thompson_product c hG sourceC hempty hgen F hn hF e) x hxT hxS hxN hx2

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
