module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CenterCoverSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.FieldReduction.FieldFourSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CubicTerminal.Complete
/-! # Original source 2.5.7: the surviving rank-two field is binary
The complete marked source classification isolates the PSL₃(4) central
cover as the sole possible nontrivial center. The cubic contradiction
excludes that case. Every nonbinary simple linear or derived symplectic
component then enters the actual prime-torus field reduction, which yields
the same excluded PSL₃(4) quotient. Hence both original model families have
exponent one, with literal PSL₃(2) and A₆ component equivalences.
No crossing, torus, field-reduction or exceptional-branch input remains.
Source: Aschbacher--Smith 2.5.7, printed pp.554--556.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}

theorem MathieuSourceSetup.component_center_eq_bot
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype) : center L=⊥ := by
  rcases MathieuSourceSetup.center_eq_bot_or_linear_four c hG hempty with h|he
  · exact h
  · obtain ⟨e⟩:=he
    exact (MathieuSourceSetup.linear_four_impossible c hG hempty hgen e).elim

omit [Finite G] in
private noncomputable def centerQuotientOfTrivial (h:center L=⊥) : L≃*(L⧸center L) :=
  MulEquiv.ofBijective (QuotientGroup.mk' (center L))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',h]),
      QuotientGroup.mk'_surjective _⟩

/-- The original linear central-cover alternative has exponent one. -/
theorem MathieuSourceSetup.linear_cover_exponent_one
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type) [Field F] [Finite F] {n:ℕ} (hn:1≤n) (hF:Nat.card F=2^n)
    (e:L⧸center L≃*PSL(3,F)) : n=1 := by
  by_contra hne
  have hn':1<n:=by omega
  let e':= (centerQuotientOfTrivial
    (MathieuSourceSetup.component_center_eq_bot c hG hempty hgen)).trans e
  obtain ⟨_,⟨e₄⟩⟩:=MathieuSourceSetup.linear_simple_field_four c hG hempty hgen F hn' hF e'
  exact MathieuSourceSetup.linear_four_impossible c hG hempty hgen e₄

/-- The original derived symplectic alternative has exponent one. -/
theorem MathieuSourceSetup.derived_symplectic_exponent_one
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (F:Type) [Field F] [Finite F] {n:ℕ} (hn:1≤n) (hF:Nat.card F=2^n)
    (e:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F)) : n=1 := by
  by_contra hne
  have hn':1<n:=by omega
  obtain ⟨_,⟨e₄⟩⟩:=MathieuSourceSetup.derived_symplectic_field_four c hG hempty hgen F hn' hF e
  exact MathieuSourceSetup.linear_four_impossible c hG hempty hgen e₄

/-- The surviving linear component is the actual PSL₃(2) carrier. -/
theorem MathieuSourceSetup.linear_cover_binary_model
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hm:IsEvenLinearThreeCover L) : Nonempty (L≃*Matrix.PSL3Two.PSL) := by
  obtain ⟨F,_,_,n,hn,hF,⟨e⟩⟩:=hm
  have hn1:=MathieuSourceSetup.linear_cover_exponent_one c hG hempty hgen F hn hF e
  let :=Fintype.ofFinite F
  let eF:F≃+*ZMod 2:=FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod,hn1,pow_one] using hF)
  exact ⟨((centerQuotientOfTrivial
    (MathieuSourceSetup.component_center_eq_bot c hG hempty hgen)).trans e).trans
      (Atlas.fieldEquivPSL 3 eF)⟩

/-- The surviving derived symplectic component is the actual A₆ carrier. -/
theorem MathieuSourceSetup.derived_symplectic_binary_model
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hm:IsDerivedSymplecticFour L) : Nonempty (L≃*alternatingGroup (Fin 6)) := by
  obtain ⟨F,_,_,n,hn,hF,⟨e⟩⟩:=hm
  have hn1:=MathieuSourceSetup.derived_symplectic_exponent_one c hG hempty hgen F hn hF e
  have hF₂:Nat.card F=2:=by simpa only [hn1,pow_one] using hF
  exact ⟨e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix hF₂)⟩

/-- Original 2.5.7 on the literal quotient by O₂(L). -/
theorem MathieuSourceSetup.lemma_2_5_7
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    {n:ℕ} (hn:1≤n)
    (hm:ClassicalGroup.IsPSL (L⧸pCore 2 L) 3 (2^n) ∨
      ClassicalGroup.IsPSp (L⧸pCore 2 L) 2 (2^n)) : n=1 := by
  have hc:=MathieuSourceSetup.center_eq_twoCore c hG localC129Input_knownSimple hempty
  rcases hm with hm|hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩:=hm
    exact MathieuSourceSetup.linear_cover_exponent_one c hG hempty hgen F hn hF
      ((QuotientGroup.quotientMulEquivOfEq hc).trans e)
  · by_contra hne
    have hn':1<n:=by omega
    obtain ⟨F,_,_,hF,⟨e⟩⟩:=hm
    let : CharP F 2:=Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    let eL:L≃*commutator (Theory.SpecificGroups.SymplecticFour.Sp F):=
      ((((centerQuotientOfTrivial
        (MathieuSourceSetup.component_center_eq_bot c hG hempty hgen)).trans
          (QuotientGroup.quotientMulEquivOfEq hc)).trans e).trans
            Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm).trans
              (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hn').symm
    exact hne (MathieuSourceSetup.derived_symplectic_exponent_one c hG hempty hgen F hn hF eL)

/-- Source 2.5.8(2): the original component is simple. -/
theorem MathieuSourceSetup.component_simple
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype) : IsSimpleGroup L := by
  let :=(c.localSetup hG structural115Input localC129Input_knownSimple).quasisimple
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  exact (centerQuotientOfTrivial
    (MathieuSourceSetup.component_center_eq_bot c hG hempty hgen)).isSimpleGroup
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
