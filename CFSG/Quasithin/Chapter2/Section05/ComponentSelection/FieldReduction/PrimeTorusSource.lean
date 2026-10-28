module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.FieldReduction.CrossingSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SplitPrimeTorusSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.FieldReduction.PrimeTorus
public import Theory.NumberTheory.BinaryMinusPrimeRestriction
/-!
# Only the cubic A.3.18 exception survives the actual split-torus action

The source crossing placement and each concrete prime-torus actor exclude
the ordinary residual equality. Every split prime is therefore three, and
the field has four elements. The exceptional conclusion retains the exact
theta quotient of the normalizer of the original displaced derived subgroup.
Source: Aschbacher–Smith 2.5.7, printed p.556.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher FieldReduction
open CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}
theorem MathieuSourceSetup.linear_simple_crossing_cubic_exception
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
    p=3 ∧ ClassicalGroup.IsPSL
      (L.subgroupOf (normalizer (D.conjBy x⁻¹:Set G))⧸
        center (L.subgroupOf (normalizer (D.conjBy x⁻¹:Set G)))) 3 (2^n) ∧
      CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.IsPGLThree
        (theta (normalizer (D.conjBy x⁻¹:Set G))⧸
          pPrimeCore 3 (theta (normalizer (D.conjBy x⁻¹:Set G)))) (2^n) := by
  let : Fact p.Prime:=⟨hp⟩
  let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let :=MathieuSourceSetup.linear_nonbinary_component_normal c hG localC129Input_knownSimple hempty
    F hn hF (quotientOfLinear F e)
  have hD:=MathieuSourceSetup.linear_simple_crossing_derived_core c hG hempty hgen F hn hF e V hV x hxT hxS hxN hx2 hmove
  have hDC:=hD.2.1.trans inf_le_right
  rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen] at hDC
  obtain ⟨X,hXL,hX,hXN,hm,_⟩:=
    MathieuSourceSetup.linear_simple_prime_torus_actor c F hn hF e ho hd
  have hXp : Nat.card X=p := hX
  have hdich:=MathieuSourceSetup.linear_simple_a318_on_crossing_derived c hG hempty hgen F hn hF e V hV x hxT hxS hxN hx2 hmove hp ho hd
  exact hdich.resolve_left (fun he => ordinary_a318_impossible L _ X x⁻¹ hp hXp
    (prime_actor_normalizes_derived hXN) hm (hDC.trans inf_le_right) he)

theorem MathieuSourceSetup.linear_simple_crossing_field_exponent_two
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*PSL(3,F))
    (V:Subgroup G) (hV:V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) (hmove:x^2∉normalizer (V:Set G)) : n=2 := by
  apply Nat.BinarySignedTorus.exponent_eq_two_of_prime_dvd_eq_three hn
  intro p hp hd
  exact (MathieuSourceSetup.linear_simple_crossing_cubic_exception c hG hempty hgen F hn hF e V hV x hxT hxS hxN hx2 hmove
    hp (Nat.BinarySignedTorus.odd_of_dvd_sub (by omega) hd) hd).1

theorem MathieuSourceSetup.linear_four_crossing_cubic_exception
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
    p=3 ∧ ClassicalGroup.IsPSL
      (L.subgroupOf (normalizer (D.conjBy x⁻¹:Set G))⧸
        center (L.subgroupOf (normalizer (D.conjBy x⁻¹:Set G)))) 3 (2^2) ∧
      CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.IsPGLThree
        (theta (normalizer (D.conjBy x⁻¹:Set G))⧸
          pPrimeCore 3 (theta (normalizer (D.conjBy x⁻¹:Set G)))) (2^2) := by
  let : Fact p.Prime:=⟨hp⟩
  let :=MathieuSourceSetup.linear_nonbinary_component_normal c hG localC129Input_knownSimple hempty
    Matrix.PSL3Four.F (by decide : 1<2) (by simpa using Matrix.PSL3Four.card_F) e
  have hD:=MathieuSourceSetup.linear_four_crossing_derived_core c hG hempty hgen e V hV x hxT hxS hxN hx2 hmove
  have hDC:=hD.2.1.trans inf_le_right
  rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen] at hDC
  have hp3 : p=3 := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp
    (by simpa using hd) |>.resolve_left hp.ne_one
  obtain ⟨X,hXL,hX,hXN,hm,_⟩:=
    MathieuSourceSetup.linear_four_cubic_torus_actor c hG hempty e
  have hXp : Nat.card X=p := hX.trans hp3.symm
  have hdich:=MathieuSourceSetup.linear_four_a318_on_crossing_derived c hG hempty hgen e V hV x hxT hxS hxN hx2 hmove hp ho hd
  exact hdich.resolve_left (fun he => ordinary_a318_impossible L _ X x⁻¹ hp hXp
    (prime_actor_normalizes_derived hXN) hm (hDC.trans inf_le_right) he)

theorem MathieuSourceSetup.derived_symplectic_crossing_cubic_exception
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
    p=3 ∧ ClassicalGroup.IsPSL
      (L.subgroupOf (normalizer (D.conjBy x⁻¹:Set G))⧸
        center (L.subgroupOf (normalizer (D.conjBy x⁻¹:Set G)))) 3 (2^n) ∧
      CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.IsPGLThree
        (theta (normalizer (D.conjBy x⁻¹:Set G))⧸
          pPrimeCore 3 (theta (normalizer (D.conjBy x⁻¹:Set G)))) (2^n) := by
  let : Fact p.Prime:=⟨hp⟩
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
  obtain ⟨X,hXL,hX,hXN,hm⟩:=
    MathieuSourceSetup.derived_symplectic_prime_torus_actor c F hn hF e ho hd
  have hXp : Nat.card X=p := hX
  have hdich:=MathieuSourceSetup.derived_symplectic_a318_on_crossing_derived c hG hempty hgen F hn hF e V hV x hxT hxS hxN hx2 hmove hp ho hd
  exact hdich.resolve_left (fun he => ordinary_a318_impossible L _ X x⁻¹ hp hXp
    (prime_actor_normalizes_derived hXN) hm (hDC.trans inf_le_right) he)

theorem MathieuSourceSetup.derived_symplectic_crossing_field_exponent_two
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type) [Field F] [Finite F] {n:ℕ} (hn:1<n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F))
    (V:Subgroup G) (hV:V∈elementaryAbelianMaxSubgroups (((S:Subgroup H).map H.subtype)⊓L))
    (x:G) (hxT:x∈c.T) (hxS:x∉(S:Subgroup H).map H.subtype)
    (hxN:x∈normalizer ((S:Subgroup H).map H.subtype:Set G))
    (hx2:x^2∈(S:Subgroup H).map H.subtype) (hmove:x^2∉normalizer (V:Set G)) : n=2 := by
  apply Nat.BinarySignedTorus.exponent_eq_two_of_prime_dvd_eq_three hn
  intro p hp hd
  exact (MathieuSourceSetup.derived_symplectic_crossing_cubic_exception c hG hempty hgen F hn hF e V hV x hxT hxS hxN hx2 hmove
    hp (Nat.BinarySignedTorus.odd_of_dvd_sub (by omega) hd) hd).1

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
