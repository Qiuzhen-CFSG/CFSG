module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingDerivedSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.FieldReduction.A318Normalizer
/-! # A.3.18 on the original displaced component derived subgroup
The three original rank-two model branches supply the literal nontrivial
normal two-subgroup used by A.3.18. Its placement and source C.1.29 are
proved internally; only the source plane and square-moving actor remain
as the preceding geometric choices. The exceptional cubic conclusion is
retained for the PSL3(4) endgame. Source: Aschbacher--Smith 2.5.7, p.556.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher FieldReduction
open CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
theorem MathieuSourceSetup.linear_simple_a318_on_crossing_derived
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F))
    (V:Subgroup G) (hV:V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) (hmove:x^2∉normalizer (V:Set G))
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hd:p∣2^n-1) :
    let D:=⁅((S:Subgroup H).map H.subtype)⊓L,((S:Subgroup H).map H.subtype)⊓L⁆
    (L.subgroupOf (normalizer (D.conjBy x⁻¹:Set G))=
      if p=3 then theta (normalizer (D.conjBy x⁻¹:Set G))
      else primeToResidual p (normalizer (D.conjBy x⁻¹:Set G))) ∨
    (p=3 ∧ ClassicalGroup.IsPSL
      (L.subgroupOf (normalizer (D.conjBy x⁻¹:Set G))⧸
        center (L.subgroupOf (normalizer (D.conjBy x⁻¹:Set G)))) 3 (2^n) ∧
      CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.IsPGLThree
        (theta (normalizer (D.conjBy x⁻¹:Set G))⧸
          pPrimeCore 3 (theta (normalizer (D.conjBy x⁻¹:Set G)))) (2^n)) := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let :=MathieuSourceSetup.linear_nonbinary_component_normal c hG localC129Input_knownSimple hempty
    F hn hF (quotientOfLinear F e)
  have hD:=MathieuSourceSetup.linear_simple_crossing_derived_core c hG hempty hgen F hn hF e V hV x hxT hxS hxN hx2 hmove
  have hDC:=hD.2.1.trans inf_le_right
  rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen] at hDC
  apply a318_dichotomy_on_displaced_core hG localC129Input_knownSimple
    c.T c.maximal c.sylow_le c.unique hempty (MathieuSourceSetup.sourceTuple c)
    ⟨c.component_le,c.component⟩ hgen hn ?_
    _ x hD.1 hDC hD.2.2 hp ho hd
  exact Or.inl ⟨F,inferInstance,inferInstance,hF,⟨quotientOfLinear F e⟩⟩
theorem MathieuSourceSetup.linear_four_a318_on_crossing_derived
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (e:L⧸center L≃*Matrix.PSL3Four.PSL)
    (V:Subgroup G) (hV:V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) (hmove:x^2∉normalizer (V:Set G))
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hd:p∣2^2-1) :
    let D:=⁅((S:Subgroup H).map H.subtype)⊓L,((S:Subgroup H).map H.subtype)⊓L⁆
    (L.subgroupOf (normalizer (D.conjBy x⁻¹:Set G))=
      if p=3 then theta (normalizer (D.conjBy x⁻¹:Set G))
      else primeToResidual p (normalizer (D.conjBy x⁻¹:Set G))) ∨
    (p=3 ∧ ClassicalGroup.IsPSL
      (L.subgroupOf (normalizer (D.conjBy x⁻¹:Set G))⧸
        center (L.subgroupOf (normalizer (D.conjBy x⁻¹:Set G)))) 3 (2^2) ∧
      CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.IsPGLThree
        (theta (normalizer (D.conjBy x⁻¹:Set G))⧸
          pPrimeCore 3 (theta (normalizer (D.conjBy x⁻¹:Set G)))) (2^2)) := by
  let :=MathieuSourceSetup.linear_nonbinary_component_normal c hG localC129Input_knownSimple hempty
    Matrix.PSL3Four.F (by decide : 1<2) (by simpa using Matrix.PSL3Four.card_F) e
  have hD:=MathieuSourceSetup.linear_four_crossing_derived_core c hG hempty hgen e V hV x hxT hxS hxN hx2 hmove
  have hDC:=hD.2.1.trans inf_le_right
  rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen] at hDC
  apply a318_dichotomy_on_displaced_core hG localC129Input_knownSimple
    c.T c.maximal c.sylow_le c.unique hempty (MathieuSourceSetup.sourceTuple c)
    ⟨c.component_le,c.component⟩ hgen (by decide : 1<2) ?_
    _ x hD.1 hDC hD.2.2 hp ho hd
  exact Or.inl ⟨Matrix.PSL3Four.F,inferInstance,inferInstance,by simpa using Matrix.PSL3Four.card_F,⟨e⟩⟩
theorem MathieuSourceSetup.derived_symplectic_a318_on_crossing_derived
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F))
    (V:Subgroup G) (hV:V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) (hmove:x^2∉normalizer (V:Set G))
    {p:ℕ} (hp:p.Prime) (ho:Odd p) (hd:p∣2^n-1) :
    let D:=⁅((S:Subgroup H).map H.subtype)⊓L,((S:Subgroup H).map H.subtype)⊓L⁆
    (L.subgroupOf (normalizer (D.conjBy x⁻¹:Set G))=
      if p=3 then theta (normalizer (D.conjBy x⁻¹:Set G))
      else primeToResidual p (normalizer (D.conjBy x⁻¹:Set G))) ∨
    (p=3 ∧ ClassicalGroup.IsPSL
      (L.subgroupOf (normalizer (D.conjBy x⁻¹:Set G))⧸
        center (L.subgroupOf (normalizer (D.conjBy x⁻¹:Set G)))) 3 (2^n) ∧
      CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.IsPGLThree
        (theta (normalizer (D.conjBy x⁻¹:Set G))⧸
          pPrimeCore 3 (theta (normalizer (D.conjBy x⁻¹:Set G)))) (2^n)) := by
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let eFull:=e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn)
  let eq:L⧸center L≃*ClassicalGroup.PSp 2 F:=QuotientGroup.congr _ _ eFull (by
    apply le_antisymm
    · rintro _ ⟨a,ha,rfl⟩
      exact (centerCongr eFull ⟨a,ha⟩).property
    · intro a ha
      exact ⟨eFull.symm a,(centerCongr eFull.symm ⟨a,ha⟩).property,eFull.apply_symm_apply a⟩)
  let :=MathieuSourceSetup.symplectic_component_normal c hG localC129Input_knownSimple hempty F hF eq
  have hD:=MathieuSourceSetup.derived_symplectic_crossing_derived_core c hG hempty hgen F hn hF e V hV x hxT hxS hxN hx2 hmove
  have hDC:=hD.2.1.trans inf_le_right
  rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen] at hDC
  apply a318_dichotomy_on_displaced_core hG localC129Input_knownSimple
    c.T c.maximal c.sylow_le c.unique hempty (MathieuSourceSetup.sourceTuple c)
    ⟨c.component_le,c.component⟩ hgen hn ?_
    _ x hD.1 hDC hD.2.2 hp ho hd
  exact Or.inr ⟨F,inferInstance,inferInstance,hF,⟨eq⟩⟩
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
