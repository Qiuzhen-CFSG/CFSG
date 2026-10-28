module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingCoreSource
public import Stellmacher.ElementaryAbelianMaxPair.ComponentFactors
/-! # Original maximum elementary factorization in Chapter 2
Every largest elementary subgroup splits as the join of its literal
component intersection and its intersection with O₂(H). Both intersections
have maximum elementary order in their own factors. The simple and derived
symplectic cases use faithful model maps; I.2.2(3b) supplies elementary full
preimages in the exceptional central PSL₃(4) cover. The shared central kernel
is retained, so no false disjointness of the two intersections is asserted.
Source: Aschbacher--Smith 2.5.7, printed p.555, the second claim.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
private theorem ker_eq_center_of_equiv {X Y:Type*} [Group X] [Group Y]
    (e:X≃*Y) (hY:center Y=⊥) : e.toMonoidHom.ker=center X := by
  rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]
  apply (bot_unique ?_).symm
  intro x hx
  have he:e x∈center Y:=(centerCongr e ⟨x,hx⟩).property
  rw [hY,mem_bot] at he
  exact e.injective (he.trans e.map_one.symm)
private noncomputable def centerQuotientCongr {X Y:Type*} [Group X] [Group Y]
    (e:X≃*Y) : (X⧸center X)≃*(Y⧸center Y) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

theorem MathieuSourceSetup.maxFamily_factors_of_cover
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hJ:elementaryAbelianMaxJ (S:Subgroup H)=((S:Subgroup H)⊓L.subgroupOf H)⊔
      (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H))
    {Y:Type*} [Group Y] (α:L→*Y) (hker:α.ker=center L)
    (hlift:∀ W:Subgroup Y,IsElementaryAbelian 2 W→IsElementaryAbelian 2 (W.comap α))
    (A:Subgroup G) (hA:A∈elementaryAbelianMaxSubgroups ((S:Subgroup H).map H.subtype)) :
    A=(A⊓L)⊔(A⊓twoCore H) ∧
      A⊓L∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L) ∧
      A⊓twoCore H∈elementaryAbelianMaxSubgroups (twoCore H) := by
  let U:=(S:Subgroup H).map H.subtype
  let R:=elementaryAbelianMaxJ U
  have hRU:R≤U:=sSup_le fun _ h=>h.1
  have hcore:twoCore H=U⊓centralizer (L:Set G):=MathieuSourceSetup.core_eq_sylow_centralizer c hgen
  have hJ':R≤(U⊓L)⊔(U⊓centralizer (L:Set G)):=by
    have hp:R=(U⊓L)⊔(R⊓centralizer (L:Set G)):=MathieuSourceSetup.ambient_thompson_product c hgen hJ
    rw [hp]
    exact sup_le_sup_left (inf_le_inf_right _ hRU) _
  have he:=maxFamily_split_component U L α hker hlift hJ' A hA
  dsimp only at he
  simpa only [←hcore] using he

theorem MathieuSourceSetup.linear_simple_maxFamily_factors
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F))
    (A:Subgroup G) (hA:A∈elementaryAbelianMaxSubgroups ((S:Subgroup H).map H.subtype)) :
    A=(A⊓L)⊔(A⊓twoCore H) ∧
      A⊓L∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L) ∧
      A⊓twoCore H∈elementaryAbelianMaxSubgroups (twoCore H) := by
  let :=MathieuSourceSetup.linear_nonbinary_component_normal c hG sourceC hempty F hn hF
    (quotientOfLinear F e)
  have hY:center PSL(3,F)=⊥:=by
    let :=Atlas.sl_perfect (F:=F) 3 (by decide)
    exact Group.IsPerfect.center_quotient_center_eq_bot (SL(3,F))
  apply MathieuSourceSetup.maxFamily_factors_of_cover c hgen
    (MathieuSourceSetup.linear_simple_thompson_product c hG sourceC hempty hgen F hn hF e)
    e.toMonoidHom (ker_eq_center_of_equiv e hY) _ A hA
  intro W hw
  let :=hw
  exact IsElementaryAbelian.comap_of_injective e.toMonoidHom e.injective W

theorem MathieuSourceSetup.linear_four_maxFamily_factors
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (e:L⧸center L≃*Matrix.PSL3Four.PSL)
    (A:Subgroup G) (hA:A∈elementaryAbelianMaxSubgroups ((S:Subgroup H).map H.subtype)) :
    A=(A⊓L)⊔(A⊓twoCore H) ∧
      A⊓L∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L) ∧
      A⊓twoCore H∈elementaryAbelianMaxSubgroups (twoCore H) := by
  let :=MathieuSourceSetup.linear_nonbinary_component_normal c hG sourceC hempty
    Matrix.PSL3Four.F (by decide : 1<2) (by simpa using Matrix.PSL3Four.card_F) e
  apply MathieuSourceSetup.maxFamily_factors_of_cover c hgen
    (MathieuSourceSetup.linear_four_thompson_product c hG sourceC hempty hgen e)
    (Matrix.PSL3Four.ElementaryParabolic.centerProjection e)
    (Matrix.PSL3Four.ElementaryParabolic.centerProjection_ker e) _ A hA
  intro W hw
  let :=hw
  exact MathieuSourceSetup.linear_four_elementary_preimage c hG sourceC hempty e W

theorem MathieuSourceSetup.derived_symplectic_maxFamily_factors
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F))
    (A:Subgroup G) (hA:A∈elementaryAbelianMaxSubgroups ((S:Subgroup H).map H.subtype)) :
    A=(A⊓L)⊔(A⊓twoCore H) ∧
      A⊓L∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L) ∧
      A⊓twoCore H∈elementaryAbelianMaxSubgroups (twoCore H) := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let eFull:=e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn)
  let :=MathieuSourceSetup.symplectic_component_normal c hG sourceC hempty F hF
    (centerQuotientCongr eFull)
  apply MathieuSourceSetup.maxFamily_factors_of_cover c hgen
    (MathieuSourceSetup.derived_symplectic_thompson_product c hG sourceC hempty hgen F hn hF e)
    eFull.toMonoidHom
    (ker_eq_center_of_equiv eFull Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot) _ A hA
  intro W hw
  let :=hw
  exact IsElementaryAbelian.comap_of_injective eFull.toMonoidHom eFull.injective W

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
