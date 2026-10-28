module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents.Selection

/-!
# Centrality of proper submodules in the strict A₆ case

If both sections are noncentral, they are faithful because K* is the
self-centralizing simple generalized Fitting subgroup. In a strong-offender
branch `Selection` constructs the marked natural subquotient, and the
original parabolic constructs its opposite upper quotient. Quadraticity
excludes that branch. In the remaining commutator-line branch the same
selection argument supplies the model needed for rank one, and then for
the transvection-centralizer contradiction of 13.8.23(4).

Generation by K makes every proper quotient noncentral. Consequently every
proper ambient submodule is K-central. The source application retains the
same critical pair, conjugator, K, U_H/V₁ and actual upper section V_H/U_H.
It discharges the central-kernel premise in the literal SourceSix application.
The ambient-invariant constituent of the maximal head is still an input;
selecting it and assembling both cases of 13.8.8 remain with
qt-d-138-six-section-recognition. Earlier geometry, field and component
premises retain their existing source owners and qt-d-1381-source.

Source: Aschbacher–Smith 13.8.22–23,26, printed pp.957–958,962.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents
open NaturalSix
variable {J E : Type*} [Group J] [Finite J]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]

variable {F : Type*} [AddCommGroup F] [Module (ZMod 2) F]

/-- Model recognition is used only on a section carrying an offender or a
commutator line. No invariant constituent is assumed for either section. -/
theorem no_two_noncentral_sections
    (ρ : Representation (ZMod 2) J E) (τ : Representation (ZMod 2) J F)
    (C : Subgroup J) (hfit : C = generalizedFitting J) (e : C ≃* Alternating)
    (W : Subrepresentation ρ)
    (hnW : ¬ (⊤ : Submodule (ZMod 2) W.toSubmodule) ≤ fixedSpace W.toRepresentation C)
    (hnQ : ¬ (⊤ : Submodule (ZMod 2) (E ⧸ W.toSubmodule)) ≤ fixedSpace W.quotientRepresentation C)
    (A : Subgroup J) (hA : IsElementaryTwo A) (hquad : IsQuadratic τ A)
    (oW : ∀ m : NaturalSection W.toRepresentation, alternatingGroup (Fin 6) ≤ m.actor.range →
      ∀ B ≤ A, IsStrongOffender W.toRepresentation B →
        Nonempty (OppositeUpper W.toRepresentation τ A))
    (oQ : ∀ m : NaturalSection W.quotientRepresentation, alternatingGroup (Fin 6) ≤ m.actor.range →
      ∀ B ≤ A, IsStrongOffender W.quotientRepresentation B →
        Nonempty (OppositeUpper W.quotientRepresentation τ A))
    (D S : Submodule (ZMod 2) E) (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (hdim : Module.finrank (ZMod 2) (E ⧸ D) ≤ rank A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hlarge : rank A = 1 → ∃ B : Subgroup J, A < B ∧
      ∀ b ∈ B, ∀ v ∈ fixedSpace ρ A, ρ b v - v ∈ S) : False := by
  have hnW' : ¬ ∃ B ≤ A, IsStrongOffender W.toRepresentation B := by
    rintro ⟨B, hBA, hB⟩
    obtain ⟨m, hm⟩ := natural_section_of_offender W.toRepresentation C hfit e hnW B hB.1 hB.2.le
    obtain ⟨o⟩ := oW m hm B hBA hB
    exact no_strong_of_opposite_quotient _ o.lower τ A hquad o.sylow o.upper
      o.surjective o.intertwines ⟨B, hBA, hB⟩
  have hnQ' : ¬ ∃ B ≤ A, IsStrongOffender W.quotientRepresentation B := by
    rintro ⟨B, hBA, hB⟩
    obtain ⟨m, hm⟩ := natural_section_of_offender W.quotientRepresentation C hfit e hnQ B hB.1 hB.2.le
    obtain ⟨o⟩ := oQ m hm B hBA hB
    exact no_strong_of_opposite_quotient _ o.lower τ A hquad o.sylow o.upper
      o.surjective o.intertwines ⟨B, hBA, hB⟩
  have hW := faithful_of_component_noncentral W.toRepresentation C hfit e hnW
  have hQ := faithful_of_component_noncentral W.quotientRepresentation C hfit e hnQ
  by_cases hzero : S = ⊥
  · have hfixed : D ≤ fixedSpace ρ A := by
      intro d hd a
      have hm := hcomm a a.property d hd
      rw [hzero] at hm
      exact sub_eq_zero.mp hm
    obtain ⟨B, hBA, _, hs⟩ :=
      strong_submodule_offender_of_fixed_subspace ρ W D hQ hA hfixed hdim
    exact hnW' ⟨B, hBA, hs⟩
  · have hpos : 0 < Module.finrank (ZMod 2) S :=
      Nat.pos_of_ne_zero (fun hz => hzero (Submodule.finrank_eq_zero.mp hz))
    have hatom : IsAtom S := Submodule.isAtom_iff_finrank_eq_one.mpr (by omega)
    have hr := rank_one_of_no_strong_offenders ρ W D S hatom hW hQ hA hcomm hdim
      (by rintro ⟨B, hBA, _, hs⟩; exact hnW' ⟨B, hBA, hs⟩)
      (by rintro ⟨B, hBA, _, hs⟩; exact hnQ' ⟨B, hBA, hs⟩)
      (fun B hB hc => by
        obtain ⟨m, _⟩ := natural_section_of_commutator_line W.toRepresentation C hfit e hnW B hB hc
        exact m.rank_one hB hc)
      (fun B hB hc => by
        obtain ⟨m, _⟩ := natural_section_of_commutator_line W.quotientRepresentation C hfit e hnQ B hB hc
        exact m.rank_one hB hc)
    obtain ⟨B, hAB, hB⟩ := hlarge hr
    exact no_rank_one_faithful_sections ρ W S hatom hW hQ hA hAB hr hbound hB
      (fun B hB hr hc => by
        obtain ⟨m, _⟩ := natural_section_of_offender W.toRepresentation C hfit e hnW B hB (by omega)
        exact m.fixed_kernel hB hc)
      (fun B hB hr hc => by
        obtain ⟨m, _⟩ := natural_section_of_offender W.quotientRepresentation C hfit e hnQ B hB (by omega)
        exact m.fixed_kernel hB hc)


open CriticalGeometry AlternatingAndLinear.FourStructure.CriticalTransfer
open AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {L T H V V₃ V₁ K : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Discharge both marked upper-quotient constructions on the original critical pair. -/
theorem source_no_two_noncentral_sections
    (c : CriticalPair L T H V)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hf : Function.Injective ρ) (hVgH : c.Vgamma ≤ H)
    (hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom)
    (hline : Nat.card V₁ = 2)
    (hcritical : Nat.log 2 ((Source.DH (Source.UH H V₃) (c.Ugamma V₃)
      (c.Aone V₁)).relIndex (Source.UH H V₃)) ≤
      Nat.log 2 ((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃)))
    (τ : Representation (ZMod 2) (Source.Hstar H) F)
    (t : UpperSection H (Source.VH H V) (Source.UH H V₃) τ)
    (hquad : ⁅c.Ugamma V₃, ⁅c.Ugamma V₃, Source.VH H V⁆⁆ ≤ Source.UH H V₃)
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hbound : fixedCodim ρ (Source.starImage H (c.Ugamma V₃)) ≤
      2 * rank (Source.starImage H (c.Ugamma V₃)))
    (hlarge : rank (Source.starImage H (c.Ugamma V₃)) = 1 →
      ∃ B : Subgroup (Source.Hstar H), Source.starImage H (c.Ugamma V₃) < B ∧
        ∀ b ∈ B, ∀ v ∈ fixedSpace ρ (Source.starImage H (c.Ugamma V₃)),
          ρ b v - v ∈ s.image (c.Aone V₁))
    (W : Subrepresentation ρ)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* Alternating)
    (hfit : Source.starImage H K = generalizedFitting (Source.Hstar H))
    (hnW : ¬ (⊤ : Submodule (ZMod 2) W.toSubmodule) ≤
      fixedSpace W.toRepresentation (Source.starImage H K))
    (hnQ : ¬ (⊤ : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁) ⧸ W.toSubmodule)) ≤
      fixedSpace W.quotientRepresentation (Source.starImage H K))
    (L₁ : Subgroup G) (hL : L₁ ≤ H) (hT : T ≤ H)
    (S : Sylow 2 (Source.Hstar H)) (hS : (S : Subgroup _) = Source.starImage H T)
    (hi : (Source.starImage H T).relIndex (Source.starImage H (L₁ ⊔ T)) = 3)
    (hflag : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hnorm : L₁ ⊔ T ≤ normalizer (V : Set G))
    (hnc : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (y : H) (hplace : c.Vgamma.map (MulAut.conj (y : G)).toMonoidHom ≤
      (L₁ ⊔ T).pCoreIn 2) : False := by
  let : Module.Finite (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := Module.Finite.of_finite
  let e := (Components.componentStarEquiv H K hKH hK).symm.trans eK
  have hUV : c.Ugamma V₃ ≤ c.Vgamma :=
    map_mono (conjugateSpanBy_mono hflag le_rfl)
  have hUgH := hUV.trans hVgH
  have hUp := (map_mono hUV).trans hplace
  obtain ⟨hd, hc⟩ := s.critical_line_displacement_of_conjugate
    (c.Ugamma V₃) (c.gb : G) hreverse hline
  exact no_two_noncentral_sections ρ τ (Source.starImage H K) hfit e W hnW hnQ _ hA
    (upper_quadratic_of_commutator τ t _ hquad)
    (fun m hm => OppositeUpper.source_oppositeUpper_of_strong m hm τ t L₁ (c.Ugamma V₃)
      hL hT hUgH S hS hi hflag hindex hnorm hnc hquad y hUp)
    (fun m hm => OppositeUpper.source_oppositeUpper_of_strong m hm τ t L₁ (c.Ugamma V₃)
      hL hT hUgH S hS hi hflag hindex hnorm hnc hquad y hUp)
    (s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)))
    (s.image (c.Aone V₁)) hd hc
    (s.critical_bound (c.Ugamma V₃) (c.Aone V₁) hUgH hf hcritical) hbound hlarge

/-- Every proper ambient submodule of the original U_H/V₁ is K-central. -/
theorem source_proper_submodule_central
    (c : CriticalPair L T H V)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hf : Function.Injective ρ) (hVgH : c.Vgamma ≤ H)
    (hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom)
    (hline : Nat.card V₁ = 2)
    (hcritical : Nat.log 2 ((Source.DH (Source.UH H V₃) (c.Ugamma V₃)
      (c.Aone V₁)).relIndex (Source.UH H V₃)) ≤
      Nat.log 2 ((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃)))
    (τ : Representation (ZMod 2) (Source.Hstar H) F)
    (t : UpperSection H (Source.VH H V) (Source.UH H V₃) τ)
    (hquad : ⁅c.Ugamma V₃, ⁅c.Ugamma V₃, Source.VH H V⁆⁆ ≤ Source.UH H V₃)
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hbound : fixedCodim ρ (Source.starImage H (c.Ugamma V₃)) ≤
      2 * rank (Source.starImage H (c.Ugamma V₃)))
    (hlarge : rank (Source.starImage H (c.Ugamma V₃)) = 1 →
      ∃ B : Subgroup (Source.Hstar H), Source.starImage H (c.Ugamma V₃) < B ∧
        ∀ b ∈ B, ∀ v ∈ fixedSpace ρ (Source.starImage H (c.Ugamma V₃)),
          ρ b v - v ∈ s.image (c.Aone V₁))
    (W : Subrepresentation ρ)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* Alternating)
    (hfit : Source.starImage H K = generalizedFitting (Source.Hstar H))
    (hproper : W ≠ ⊤)
    (hρ : TransvectionRecognition.IsConjugation H V₃ V₁ ρ)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (L₁ : Subgroup G) (hL : L₁ ≤ H) (hT : T ≤ H)
    (S : Sylow 2 (Source.Hstar H)) (hS : (S : Subgroup _) = Source.starImage H T)
    (hi : (Source.starImage H T).relIndex (Source.starImage H (L₁ ⊔ T)) = 3)
    (hflag : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hnorm : L₁ ⊔ T ≤ normalizer (V : Set G))
    (hnc : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (y : H) (hplace : c.Vgamma.map (MulAut.conj (y : G)).toMonoidHom ≤
      (L₁ ⊔ T).pCoreIn 2) : W.toSubmodule ≤ fixedSpace ρ (Source.starImage H K) := by
  let : Module.Finite (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := Module.Finite.of_finite
  by_contra hn
  have hnW : ¬ (⊤ : Submodule (ZMod 2) W.toSubmodule) ≤
      fixedSpace W.toRepresentation (Source.starImage H K) := by
    intro hfix
    apply hn
    intro v hv k
    exact congrArg Subtype.val (hfix (show (⟨v, hv⟩ : W.toSubmodule) ∈ ⊤ from trivial) k)
  have hg : subspaceCommutator ρ ⊤ (Source.starImage H K) = ⊤ :=
    (TransvectionRecognition.Component.commutatorImage_eq_subspaceCommutator K hKH ρ hρ).symm.trans
      (TransvectionRecognition.Component.ModelExtension.commutatorImage_eq_top hgen)
  have hnQ : ¬ (⊤ : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁) ⧸ W.toSubmodule)) ≤
      fixedSpace W.quotientRepresentation (Source.starImage H K) := by
    intro hfix
    apply hproper
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    rw [← hg]
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, v, _, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp
    change W.toSubmodule.mkQ (ρ k v - v) = 0
    rw [map_sub, ← Subrepresentation.quotientRepresentation_mk]
    exact sub_eq_zero.mpr (hfix (by trivial) ⟨k, hk⟩)
  exact source_no_two_noncentral_sections c ρ s hf hVgH hreverse hline hcritical
    τ t hquad hA hbound hlarge W hKH hK eK hfit hnW hnQ
    L₁ hL hT S hS hi hflag hindex hnorm hnc y hplace

open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open scoped Pointwise

/-- Apply SourceSix after proving centrality of the chosen maximal kernel.
Only selection of the ambient-invariant head constituent remains explicit. -/
theorem source_alternative_of_selected_head
    (T₀ : Sylow 2 G) {L₀ V₂ M G₁ : Subgroup G}
    (d : LocalSetup T₀ L₀ V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T₀ L₀ V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L₀ T₀ V₁) (T₀ : Subgroup G) G₁ M)
    (c : CriticalPair L T H V)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hf : Function.Injective ρ) (hVgH : c.Vgamma ≤ H)
    (hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom)
    (hline : Nat.card V₁ = 2)
    (hcritical : Nat.log 2 ((Source.DH (Source.UH H V₃) (c.Ugamma V₃)
      (c.Aone V₁)).relIndex (Source.UH H V₃)) ≤
      Nat.log 2 ((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃)))
    (τ : Representation (ZMod 2) (Source.Hstar H) F)
    (t : UpperSection H (Source.VH H V) (Source.UH H V₃) τ)
    (hquad : ⁅c.Ugamma V₃, ⁅c.Ugamma V₃, Source.VH H V⁆⁆ ≤ Source.UH H V₃)
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hbound : fixedCodim ρ (Source.starImage H (c.Ugamma V₃)) ≤
      2 * rank (Source.starImage H (c.Ugamma V₃)))
    (hlarge : rank (Source.starImage H (c.Ugamma V₃)) = 1 →
      ∃ B : Subgroup (Source.Hstar H), Source.starImage H (c.Ugamma V₃) < B ∧
        ∀ b ∈ B, ∀ v ∈ fixedSpace ρ (Source.starImage H (c.Ugamma V₃)),
          ρ b v - v ∈ s.image (c.Aone V₁))
    (W : Subrepresentation ρ)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* Alternating)
    (hfit : Source.starImage H K = generalizedFitting (Source.Hstar H))
    (hmax : IsCoatom W)
    (IQ : Subrepresentation W.quotientRepresentation)
    (hIQ : IsIrrPlus W.quotientRepresentation (Source.starImage H K) IQ.toSubmodule)
    (hρ : TransvectionRecognition.IsConjugation H V₃ V₁ ρ)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (L₁ : Subgroup G) (hL : L₁ ≤ H) (hT : T ≤ H)
    (S : Sylow 2 (Source.Hstar H)) (hS : (S : Subgroup _) = Source.starImage H T)
    (hi : (Source.starImage H T).relIndex (Source.starImage H (L₁ ⊔ T)) = 3)
    (hflag : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hnorm : L₁ ⊔ T ≤ normalizer (V : Set G))
    (hnc : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (y : H) (hplace : c.Vgamma.map (MulAut.conj (y : G)).toMonoidHom ≤
      (L₁ ⊔ T).pCoreIn 2) :
    let := d.uh_elementary hH
    ∃ eK' : (K ⧸ pCore 2 K) ≃* Alternating,
      TransvectionRecognition.Component.HasSectionModel H V₃ V₁ ρ K hKH alternatingAction eK' ∧
      (H : Set G) = (K : Set G) * (T₀ : Set G) ∧
      Nonempty ((L₀ ⧸ pCore 2 L₀) ≃* Alternating) ∧
      SourceSix.MarkedFullAction hKH eK' ρ ∧
      CriticalGeometry.Reorientation.TwoNoncentralChiefFactors
        (ChiefQuotient.loneQuotientRepresentation H V₃ V₁ (sourceOne L₀ T₀ V₁)
          (le_sup_left.trans hH.1.2) ρ) := by
  have hW := source_proper_submodule_central c ρ s hf hVgH hreverse hline hcritical
    τ t hquad hA hbound hlarge W hKH hK eK hfit hmax.1 hρ hgen
    L₁ hL hT S hS hi hflag hindex hnorm hnc y hplace
  exact source_alternative_of_central_head_constituent T₀ d earlier hH hKH hK ρ hρ hgen
    eK hfit W hmax hW IQ hIQ _ hA hbound

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents
