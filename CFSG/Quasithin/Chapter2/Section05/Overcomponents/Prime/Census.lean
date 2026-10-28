module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.Rows
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.ModelExclusionsSource
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.ModelExclusionsOddBender
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.ModelExclusionsSporadicSource
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.Exceptional
public import CFSG.Quasithin.Chapter1.SourceInputs.InvolutionCentralizers
public import Theory.Mathieu.M22.Properties.OuterCentralizers.EightFixedComponents
/-!
# The literal prime-component overcomponent census

Apply the actual marked Chapter 1 model-action catalogue to the component of the original involution centralizer. Its ordinary fixed component is the original prime-field PSL2 component. The intrinsic family exclusions leave the field PSL3(4) and outer J2 rows. The original marked action also proves that the containing center is a two-group. The fixed-octad M22 exclusion is discharged internally, and no nonnormality assumption on the original component is needed.

Source: Aschbacher–Smith 2.5.19, printed pp.560–563.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
open ComponentRefinement ComponentSelection PrimeRows
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

private theorem simple_perfect_center_eq_bot {E : Type*} [Group E]
    [IsSimpleGroup E] [Group.IsPerfect E] : center E = ⊥ :=
  (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center E) inferInstance).resolve_right
    (fun h => Group.IsPerfect.not_isMulCommutative E (center_eq_top_iff.mp h))

/-- The literal marked 1.1.5 catalogue leaves precisely the field PSL₃(4)
and outer J₂ rows, including the two-primary center of the original cover. -/
theorem source_modelAction_prime_quotient
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p)
    (eK : K ≃* PSL(2,ZMod p))
    {E : Type*} [Group E] [Finite E] [IsQuasisimple E]
    (α : MulAut E) (hα : ModelAction115 E α)
    (hinv : ∀ x ∈ pPrimeCore 2 E, α x = x⁻¹)
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eKB : K ≃* B) :
    PrimeFixedQuotientModels (E ⧸ center E) (quotientAut (center E) a) ∧
      IsPGroup 2 (center E) := by
  let : Fact p.Prime := ⟨hp.1⟩
  have linear {n : ℕ} (hn : 0 < n)
      (hm : ClassicalGroup.IsPSL (E ⧸ center E) 3 (2^n)) :
      PrimeFixedQuotientModels (E ⧸ center E) (quotientAut (center E) a) := by
    obtain ⟨rfl,_,F,hF,hfinite,hcard,e,hfield⟩ := source_linear_quotient_field
      c hG hempty hgen hb hn hm a ha B hB eKB
    exact Or.inl ⟨F,hF,hfinite,by simpa using hcard,e,hfield⟩
  cases hα with
  | lie hs hm hi =>
    let : IsSimpleGroup E := hs
    have hz : center E = ⊥ := simple_perfect_center_eq_bot
    have hzp : IsPGroup 2 (center E) := by rw [hz]; exact IsPGroup.of_subsingleton 2 _
    let eZ : (E ⧸ center E) ≃* E :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
    refine ⟨?_,hzp⟩
    rcases hm with hm | hm | ⟨n,hn,hm⟩
    · exact (source_bender_no_injective_of_prime c hG hempty hgen hb hp.1 eK hm
        (a.fixedSubgroup.subtype.comp (B.subtype.comp eKB.toMonoidHom))
        (a.fixedSubgroup.subtype_injective.comp (B.subtype_injective.comp eKB.injective))).elim
    · cases hm with
      | linear n hn hm => exact linear (by omega) (hm.of_mulEquiv eZ)
      | symplectic n hn hm =>
        obtain ⟨_,⟨e⟩,_⟩ := source_symplectic_fixed_component c hG hempty hgen hb
          (by omega) hm a ha B hB eKB
        exact (prime_pslTwo_not_alternating hp.1 hp7 (Or.inr (Or.inl rfl))
          ⟨eK.symm.trans e⟩).elim
      | g2 n hn hm =>
        exact (source_not_g2_fixed_component c hG hempty hgen hb hp7 eK hn hm
          a ha B hB eKB).elim
      | triality n hn hm =>
        exact (source_not_triality_fixed_component c hG hempty hgen hb (by omega)
          hm a ha B hB eKB).elim
      | ree m hm he =>
        exact (source_not_ree_fixed_component c hG hempty hgen hb hm he a ha B eKB).elim
      | symplectic_derived he =>
        exact (not_symplectic_derived_fixed_component hp7 eK he.some a B eKB).elim
      | g2_derived he => exact (not_g2_derived_fixed_component he.some a ha B hB).elim
      | tits he => exact (not_tits_fixed_component he.some a ha B hB).elim
    · exact (binary_model_fixed_no_prime_component hn hm hp.1 hp7 a ha B hB
        (eK.symm.trans eKB)).elim
  | two_cover hn hz hm hi =>
    have hzp : IsPGroup 2 (center E) := by rw [hz]; exact pCore_isPGroup
    refine ⟨?_,hzp⟩
    let eZ := QuotientGroup.quotientMulEquivOfEq hz
    rcases hm with hm | hm
    · apply linear (n := 2) (by decide)
      simpa using hm.of_mulEquiv eZ
    · let : IsSimpleGroup (E ⧸ center E) := IsQuasisimple.simple
      obtain ⟨_,haq,hC,⟨eC⟩⟩ := source_fixed_component_central_quotient
        c hG hempty hgen hb a ha B hB eKB
      exact (source_not_g2_fixed_component c hG hempty hgen hb hp7 eK
        (n := 2) (by decide) (by simpa using hm.of_mulEquiv eZ) _ haq _ hC eC).elim
  | six σ hs hm =>
    rcases hm with ⟨e,_⟩ | ⟨_,_,e,_⟩
    · exact (alternating_model_fixed_no_prime_component (Or.inl rfl) e hp.1 hp7
        a ha B hB (eK.symm.trans eKB)).elim
    · exact (source_alternating_quotient_exclusion_of_prime c hG hempty hgen hb
        hp.1 hp7 eK a ha B hB eKB (Or.inl rfl) e).elim
  | seven σ hs hm =>
    rcases hm with ⟨e,_⟩ | ⟨_,_,e,_⟩
    · exact (alternating_model_fixed_no_prime_component (Or.inr rfl) e hp.1 hp7
        a ha B hB (eK.symm.trans eKB)).elim
    · exact (source_alternating_quotient_exclusion_of_prime c hG hempty hgen hb
        hp.1 hp7 eK a ha B hB eKB (Or.inr rfl) e).elim
  | odd hm hi =>
    exact (source_odd_model_exclusion_of_prime hp hp7 hm a ha B hB (eK.symm.trans eKB)).elim
  | sporadic name hj3 he hinner =>
    have hz := MulAut.center_eq_twoCore_of_inner_inverts_oddCore α hinner.1 hinv
    let e : (E ⧸ center E) ≃* name.Carrier :=
      (QuotientGroup.quotientMulEquivOfEq hz).trans he.some
    have hname := source_sporadic_quotient_eq_j2
      _root_.Sporadic.Mathieu.M22OuterCentralizers.eight_fixed_no_component c hG hempty hgen hb
      hp hp7 eK a ha B hB eKB name hj3 e
    subst name
    have hout := (source_j2_quotient_outer c hG hempty hgen hb a ha B hB eKB e).1
    exact ⟨Or.inr ⟨e,hout⟩,by rw [hz]; exact pCore_isPGroup⟩

/-- Every actual invariant component of an involution centralizer with original
prime fixed component has the retained marked quotient row. -/
theorem source_prime_overcomponent_quotient
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p)
    (eK : K ≃* PSL(2,ZMod p))
    (i : G) (hi : orderOf i = 2)
    (X : Subgroup (centralizer ({i} : Set G)))
    (hX : IsComponent (centralizer ({i} : Set G)) X)
    (a : MulAut X) (ha : orderOf a = 2)
    (B : Subgroup a.fixedSubgroup) (hB : IsComponent a.fixedSubgroup B)
    (eKB : K ≃* B) :
    PrimeFixedQuotientModels (X ⧸ center X) (quotientAut (center X) a) ∧
      IsPGroup 2 (center X) := by
  let : IsQuasisimple X := hX.2
  obtain ⟨P,N,w,h115,_,_,α,hα,hm⟩ :=
    Chapter1.involution_component_source_catalogue hG i hi X hX
  obtain ⟨_,β,Q,hβ,hmark,_⟩ := h115.component_inputs X hX
  have he : β = α := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact (hβ x).trans (hα x).symm
  subst β
  exact source_modelAction_prime_quotient c hG hempty hgen hb hp hp7 eK
    α hm hmark.inverts_odd_core a ha B hB eKB
end CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
