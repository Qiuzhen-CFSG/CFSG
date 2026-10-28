module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.FieldReduction.PrimeTorusSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SquareMovingSource
public import Theory.SpecificGroups.LinearCoefficientEquiv
/-!
# The original nonbinary source branches reduce to PSL₃(4)

The verified source plane choice supplies the original square-moving crossing.
The actual torus action excludes every ordinary A.3.18 case, forcing n = 2.
Transport through the relative component and its center gives an equivalence
of the original component central quotient with the fixed PSL₃(4) carrier.
No geometric witness, torus actor, or field-reduction premise is assumed.
Source: Aschbacher–Smith 2.5.7, printed p.556, before the cubic Frattini step.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher FieldReduction
open CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels

private noncomputable def centerQuotientCongr {X Y:Type*} [Group X] [Group Y]
    (e:X≃*Y) : (X⧸center X)≃*(Y⧸center Y) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

private theorem original_four_model {G:Type*} [Group G] {L N:Subgroup G}
    (hLN:L≤N)
    (h:ClassicalGroup.IsPSL (L.subgroupOf N⧸center (L.subgroupOf N)) 3 4) :
    Nonempty (L⧸center L≃*Matrix.PSL3Four.PSL) := by
  obtain ⟨F,iF,iFin,hF,⟨e⟩⟩:=h
  let :=iF
  let :=iFin
  let :=Fintype.ofFinite F
  let :=Fintype.ofFinite Matrix.PSL3Four.F
  let eF : F≃+*Matrix.PSL3Four.F:=FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hF,Matrix.PSL3Four.card_F])
  exact ⟨((centerQuotientCongr (subgroupOfEquivOfLe hLN).symm).trans e).trans
    (Matrix.ProjectiveSpecialLinearGroup.ringEquiv eF)⟩

variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
theorem MathieuSourceSetup.linear_simple_field_four
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F))
 :
    n=2 ∧ Nonempty (L⧸center L≃*Matrix.PSL3Four.PSL) := by
  obtain ⟨V,hV,x,hxT,hxS,hxN,hx2,hmove⟩:=
    MathieuSourceSetup.linear_simple_square_moving_plane c hG hempty hgen F hn hF e
  have hn2:=MathieuSourceSetup.linear_simple_crossing_field_exponent_two
    c hG hempty hgen F hn hF e V hV x hxT hxS hxN hx2 hmove
  have hd:3∣2^n-1:=by rw [hn2];decide
  have hE:=MathieuSourceSetup.linear_simple_crossing_cubic_exception
    c hG hempty hgen F hn hF e V hV x hxT hxS hxN hx2 hmove
    (by decide : Nat.Prime 3) (by decide : Odd 3) hd
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let :=MathieuSourceSetup.linear_nonbinary_component_normal c hG localC129Input_knownSimple hempty
    F hn hF (quotientOfLinear F e)
  have hD:=MathieuSourceSetup.linear_simple_crossing_derived_core
    c hG hempty hgen F hn hF e V hV x hxT hxS hxN hx2 hmove
  have hDC:=hD.2.1.trans inf_le_right
  rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen] at hDC
  have hLN:= (le_centralizer_iff.mp (hDC.trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  exact ⟨hn2,original_four_model hLN (by simpa only [hn2,show (2:ℕ)^2=4 by decide] using hE.2.1)⟩

theorem MathieuSourceSetup.derived_symplectic_field_four
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F))
 :
    n=2 ∧ Nonempty (L⧸center L≃*Matrix.PSL3Four.PSL) := by
  obtain ⟨V,hV,x,hxT,hxS,hxN,hx2,hmove⟩:=
    MathieuSourceSetup.derived_symplectic_square_moving_plane c hG hempty hgen F hn hF e
  have hn2:=MathieuSourceSetup.derived_symplectic_crossing_field_exponent_two
    c hG hempty hgen F hn hF e V hV x hxT hxS hxN hx2 hmove
  have hd:3∣2^n-1:=by rw [hn2];decide
  have hE:=MathieuSourceSetup.derived_symplectic_crossing_cubic_exception
    c hG hempty hgen F hn hF e V hV x hxT hxS hxN hx2 hmove
    (by decide : Nat.Prime 3) (by decide : Odd 3) hd
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let eFull:=e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn)
  let eq:L⧸center L≃*ClassicalGroup.PSp 2 F:=QuotientGroup.congr _ _ eFull (by
    apply le_antisymm
    · rintro _ ⟨a,ha,rfl⟩
      exact (centerCongr eFull ⟨a,ha⟩).property
    · intro a ha
      exact ⟨eFull.symm a,(centerCongr eFull.symm ⟨a,ha⟩).property,eFull.apply_symm_apply a⟩)
  let :=MathieuSourceSetup.symplectic_component_normal c hG localC129Input_knownSimple hempty F hF eq
  have hD:=MathieuSourceSetup.derived_symplectic_crossing_derived_core
    c hG hempty hgen F hn hF e V hV x hxT hxS hxN hx2 hmove
  have hDC:=hD.2.1.trans inf_le_right
  rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen] at hDC
  have hLN:= (le_centralizer_iff.mp (hDC.trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)
  exact ⟨hn2,original_four_model hLN (by simpa only [hn2,show (2:ℕ)^2=4 by decide] using hE.2.1)⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
