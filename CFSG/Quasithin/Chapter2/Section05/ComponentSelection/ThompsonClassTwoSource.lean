module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SylowCommutatorSource
public import Stellmacher.ElementaryAbelianMaxPair.CrossingClassTwo
/-! # Class two for the original Thompson subgroup
The faithful crossing-core embedding and the proved component Sylow rows
make both commuting factors class two. The original source hypotheses
discharge every Sylow placement and component normality input.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
theorem MathieuSourceSetup.relative_sylow_class_two
    (c:MathieuSourceSetup H L M S z)
    (hclass:∀P:Sylow 2 L,_root_.commutator P≤center P) :
    _root_.commutator (((S:Subgroup H).map H.subtype).subgroupOf L)≤
      center (((S:Subgroup H).map H.subtype).subgroupOf L) := by
  obtain ⟨Q,hQ⟩:=S.exists_subgroupOf_eq_of_subnormal (L.subgroupOf H) c.component.1
  let eL:L.subgroupOf H≃*L:=subgroupOfEquivOfLe c.component_le
  let P:=Q.mapSurjective (f:=eL.toMonoidHom) eL.surjective
  have hP:(P:Subgroup L)=((S:Subgroup H).map H.subtype).subgroupOf L:=by
    ext l
    change l∈(Q:Subgroup (L.subgroupOf H)).map eL.toMonoidHom ↔ _
    rw [mem_map_equiv,hQ]
    change (⟨(l:G),c.component_le l.property⟩:H)∈S ↔ (l:G)∈(S:Subgroup H).map H.subtype
    constructor
    · intro h
      exact mem_map_of_mem H.subtype h
    · rintro ⟨a,ha,he⟩
      have hh:a=(⟨(l:G),c.component_le l.property⟩:H):=Subtype.ext he
      exact hh ▸ ha
  have hp:=hclass P
  rwa [hP] at hp

theorem MathieuSourceSetup.thompson_class_two_of_sylow
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hJ:elementaryAbelianMaxJ (S:Subgroup H)=((S:Subgroup H)⊓L.subgroupOf H)⊔
      (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H))
    (hclass:∀P:Sylow 2 L,_root_.commutator P≤center P)
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    _root_.commutator (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))≤
      center (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)) := by
  let Y:=(S:Subgroup H).map H.subtype
  have hcore:=MathieuSourceSetup.core_eq_sylow_centralizer c hgen
  have hd:Disjoint (Y⊓centralizer (L:Set G)) ((Y⊓centralizer (L:Set G)).conjBy x⁻¹):=by
    rw [←hcore]
    exact (generated_twoCore_disjoint S (MathieuSourceSetup.sourceTuple c) ⟨c.component_le,c.component⟩ hgen hxT hxS hxN hx2).1
  exact crossing_thompson_class_two Y L (MathieuSourceSetup.ambient_thompson_product c hgen hJ)
    (MathieuSourceSetup.relative_sylow_class_two c hclass) x⁻¹
    ((normalizer (Y:Set G)).inv_mem hxN) hd
private noncomputable def centerQuotientCongr {X Y:Type*} [Group X] [Group Y]
    (e:X≃*Y) : (X⧸center X)≃*(Y⧸center Y) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
theorem MathieuSourceSetup.linear_simple_thompson_class_two
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    _root_.commutator (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))≤
      center (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)) := by
  let :=MathieuSourceSetup.linear_nonbinary_component_normal c hG sourceC hempty F hn hF
    (quotientOfLinear F e)
  exact MathieuSourceSetup.thompson_class_two_of_sylow c hgen
    (MathieuSourceSetup.linear_simple_thompson_product c hG sourceC hempty hgen F hn hF e)
    (fun P=>(linear_simple_sylow_commutator_rows F hn hF e P).1) x hxT hxS hxN hx2

theorem MathieuSourceSetup.linear_four_thompson_class_two
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (e:L⧸center L≃*Matrix.PSL3Four.PSL)
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) :
    _root_.commutator (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))≤
      center (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)) := by
  let :=MathieuSourceSetup.linear_nonbinary_component_normal c hG sourceC hempty
    Matrix.PSL3Four.F (by decide : 1<2) (by simpa using Matrix.PSL3Four.card_F) e
  exact MathieuSourceSetup.thompson_class_two_of_sylow c hgen
    (MathieuSourceSetup.linear_four_thompson_product c hG sourceC hempty hgen e)
    (fun P=>(MathieuSourceSetup.linear_four_sylow_commutator_rows c hG sourceC hempty e P).1)
    x hxT hxS hxN hx2

theorem MathieuSourceSetup.derived_symplectic_thompson_class_two
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
    _root_.commutator (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype))≤
      center (elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)) := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let eFull:=e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn)
  let :=MathieuSourceSetup.symplectic_component_normal c hG sourceC hempty F hF
    (centerQuotientCongr eFull)
  exact MathieuSourceSetup.thompson_class_two_of_sylow c hgen
    (MathieuSourceSetup.derived_symplectic_thompson_product c hG sourceC hempty hgen F hn hF e)
    (fun P=>(derived_symplectic_sylow_commutator_rows F hn hF e P).1) x hxT hxS hxN hx2
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
