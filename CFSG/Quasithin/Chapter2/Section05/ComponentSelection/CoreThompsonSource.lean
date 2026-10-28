module
public import Stellmacher.ElementaryAbelianMaxPair.CoreGenerated
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.ThompsonFactorSource
/-! # The original core factor is its own elementary Thompson layer
The proved maximum-family factorization identifies J(S) intersect O₂(H)
with J(O₂(H)). Central-product order comparisons supply the reverse
containment, including the shared elementary covering center. All three
original rank-two source branches discharge the center and factorization
inputs. This is the generated-core step preceding the two-plane fusion.
Source: Aschbacher--Smith 2.5.7, printed p.555.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
private theorem center_elementary_of_equiv {X Y:Type*} [Group X] [Group Y]
    (e:X≃*Y) (hY:center Y=⊥) : IsElementaryAbelian 2 (center X) := by
  have hx:center X=⊥:=by
    apply bot_unique
    intro x hx
    have he:e x∈center Y:=(centerCongr e ⟨x,hx⟩).property
    rw [hY,mem_bot] at he
    exact e.injective (he.trans e.map_one.symm)
  let : Subsingleton (center X):=⟨fun x y=>Subtype.ext (by
    have hx' : (x:X)=1:=mem_bot.mp (hx ▸ x.property)
    have hy' : (y:X)=1:=mem_bot.mp (hx ▸ y.property)
    exact hx'.trans hy'.symm)⟩
  refine {
    toIsMulCommutative := ⟨⟨fun x y => Subsingleton.elim _ _⟩⟩
    exponent_dvd_p := ?_ }
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => Subsingleton.elim _ _)
private noncomputable def centerQuotientCongr {X Y:Type*} [Group X] [Group Y]
    (e:X≃*Y) : (X⧸center X)≃*(Y⧸center Y) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

theorem MathieuSourceSetup.thompson_core_eq_core_thompson_of_factors
    (c:MathieuSourceSetup H L M S z) [(L.subgroupOf H).Normal]
    [IsElementaryAbelian 2 (center L)]
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hJ:elementaryAbelianMaxJ (S:Subgroup H)=((S:Subgroup H)⊓L.subgroupOf H)⊔
      (elementaryAbelianMaxJ (S:Subgroup H)⊓pCore 2 H))
    (hfac:∀ A∈elementaryAbelianMaxSubgroups ((S:Subgroup H).map H.subtype),
      A=(A⊓L)⊔(A⊓twoCore H) ∧ A⊓twoCore H∈elementaryAbelianMaxSubgroups (twoCore H)) :
    elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H=
      elementaryAbelianMaxJ (twoCore H) := by
  let U:=(S:Subgroup H).map H.subtype
  let K:=U⊓L
  let C:=twoCore H
  let R:=elementaryAbelianMaxJ U
  have hRU:R≤U:=sSup_le fun _ h=>h.1
  have hcore:C=U⊓centralizer (L:Set G):=MathieuSourceSetup.core_eq_sylow_centralizer c hgen
  have hCU:C≤U:=hcore.symm ▸ (show U⊓centralizer (L:Set G)≤U from inf_le_left)
  have hCC:C≤centralizer (L:Set G):=hcore.symm ▸ (show U⊓centralizer (L:Set G)≤centralizer (L:Set G) from inf_le_right)
  have hc:K≤centralizer (C:Set G):=le_centralizer_iff.mp (hCC.trans (centralizer_le inf_le_right))
  have hRC:R≤K⊔C:=by
    have hp:R=K⊔(R⊓centralizer (L:Set G)):=MathieuSourceSetup.ambient_thompson_product c hgen hJ
    rw [hp]
    apply sup_le_sup_left
    rw [hcore]
    exact inf_le_inf_right _ hRU
  have hZ:K⊓C≤(center L).map L.subtype:=by
    rintro x ⟨hx,hc⟩
    refine ⟨⟨x,hx.2⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    exact Subtype.ext (hCC hc y y.property)
  let : IsElementaryAbelian 2 ((center L).map L.subtype):=IsElementaryAbelian.map L.subtype
  let : IsElementaryAbelian 2 (K⊓C:Subgroup G):=IsElementaryAbelian.of_le hZ
  apply thompson_centralizer_factor U K C inf_le_left hCU hc
  · intro A hA
    obtain ⟨he,hf⟩:=hfac A hA
    have hAK:A⊓K=A⊓L:=by dsimp only [K];rw [←inf_assoc,inf_eq_left.mpr hA.1]
    exact ⟨by simpa only [hAK] using he,hf⟩
  · intro A hA
    exact maxFamily_central_intersection_le U K C A hc inf_le_left hA ((le_sSup hA).trans hRC)

theorem MathieuSourceSetup.linear_simple_thompson_core
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F)) :
    elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H=
      elementaryAbelianMaxJ (twoCore H) := by
  let :=MathieuSourceSetup.linear_nonbinary_component_normal c hG sourceC hempty F hn hF
    (quotientOfLinear F e)
  have hY:center PSL(3,F)=⊥:=by
    let :=Atlas.sl_perfect (F:=F) 3 (by decide)
    exact Group.IsPerfect.center_quotient_center_eq_bot (SL(3,F))
  let : IsElementaryAbelian 2 (center L):=center_elementary_of_equiv e hY
  apply MathieuSourceSetup.thompson_core_eq_core_thompson_of_factors c hgen
    (MathieuSourceSetup.linear_simple_thompson_product c hG sourceC hempty hgen F hn hF e)
  intro A hA
  have h:=MathieuSourceSetup.linear_simple_maxFamily_factors c hG sourceC hempty hgen F hn hF e A hA
  exact ⟨h.1,h.2.2⟩

theorem MathieuSourceSetup.linear_four_thompson_core
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (e:L⧸center L≃*Matrix.PSL3Four.PSL) :
    elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H=
      elementaryAbelianMaxJ (twoCore H) := by
  let :=MathieuSourceSetup.linear_nonbinary_component_normal c hG sourceC hempty
    Matrix.PSL3Four.F (by decide : 1<2) (by simpa using Matrix.PSL3Four.card_F) e
  have hZ:IsPGroup 2 (center L):=by
    rw [MathieuSourceSetup.center_eq_twoCore c hG sourceC hempty]
    exact pCore_isPGroup
  let : Fact (IsPGroup 2 (center L)):=⟨hZ⟩
  let : IsElementaryAbelian 2 (center L):=
    (frattini_eq_bot_iff_isElementaryAbelian (p:=2)).mp
      (MathieuSourceSetup.linear_four_center_frattini c hG sourceC hempty e)
  apply MathieuSourceSetup.thompson_core_eq_core_thompson_of_factors c hgen
    (MathieuSourceSetup.linear_four_thompson_product c hG sourceC hempty hgen e)
  intro A hA
  have h:=MathieuSourceSetup.linear_four_maxFamily_factors c hG sourceC hempty hgen e A hA
  exact ⟨h.1,h.2.2⟩

theorem MathieuSourceSetup.derived_symplectic_thompson_core
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (sourceC:LocalC129Input KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type*) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F)) :
    elementaryAbelianMaxJ ((S:Subgroup H).map H.subtype)⊓twoCore H=
      elementaryAbelianMaxJ (twoCore H) := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let eFull:=e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn)
  let :=MathieuSourceSetup.symplectic_component_normal c hG sourceC hempty F hF
    (centerQuotientCongr eFull)
  let : IsElementaryAbelian 2 (center L):=center_elementary_of_equiv eFull
    Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot
  apply MathieuSourceSetup.thompson_core_eq_core_thompson_of_factors c hgen
    (MathieuSourceSetup.derived_symplectic_thompson_product c hG sourceC hempty hgen F hn hF e)
  intro A hA
  have h:=MathieuSourceSetup.derived_symplectic_maxFamily_factors c hG sourceC hempty hgen F hn hF e A hA
  exact ⟨h.1,h.2.2⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
