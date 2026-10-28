module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents.Centrality
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents.Parabolic

/-!
# The strict critical case of the original A₆ section recognition

Choose a maximal ambient submodule of the literal U_H/V₁. The completed
multiple-factor contradiction makes its kernel K-central. Generation
by K makes its head faithful, and the original L₁T parabolic supplies
an irreducible A₆ head with an actual natural model. The central-head
construction gives the intrinsic K/O₂(K) marking and HasSectionModel;
SourceSix then supplies both full modules, the full A₆/S₆ actors, and
the L₁ chief-factor conclusion.

Together with `Constituents.Transvection.source_alternative_of_transvection`,
this handles both cases of 13.8.8. All constituent selection, centrality
and opposite-upper constructions are discharged. The explicit inputs
are the genuine earlier 13.8.21–23, F.9.13 and 13.8.4 facts; their source
owners, including qt-d-1381-source and the existing field/component/geometry
owners, retain their chapter discharge. The final 13.8.27 assembly remains
with qt-d-138-six-g2-source.

Source: Aschbacher–Smith 13.8.26, printed p.962/PDF p.979.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents
open NaturalSix
open CriticalGeometry AlternatingAndLinear.FourStructure.CriticalTransfer
open AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open scoped IsMulCommutative Pointwise
variable {G F : Type*} [Group G] [Finite G] [AddCommGroup F] [Module (ZMod 2) F]
  {L T H V V₃ V₁ K : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The strict critical case: construct the kernel, head and full SourceSix alternative. -/
theorem source_alternative_strict
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
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* Alternating)
    (hfit : Source.starImage H K = generalizedFitting (Source.Hstar H))
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
  let := d.uh_elementary hH
  let : Module.Finite (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := Module.Finite.of_finite
  let C := Source.starImage H K
  let : C.Normal := by change (Source.starImage H K).Normal; rw [hfit]; infer_instance
  let e := (Components.componentStarEquiv H K hKH hK).symm.trans eK
  let : Nontrivial C := e.symm.injective.nontrivial
  obtain ⟨k, hk⟩ := exists_ne (1 : C)
  obtain ⟨v, hv⟩ : ∃ v, ρ k v ≠ v := by
    by_contra! hh
    apply hk
    apply Subtype.ext
    apply hf
    ext v
    simpa using hh v
  let : Nontrivial (Additive (Source.Utilde H V₃ V₁)) := ⟨⟨ρ k v, v, hv⟩⟩
  let : IsCoatomic (Subrepresentation ρ) := SimpleHeadQuotient.subrepresentation_coatomic ρ
  obtain ⟨W, hmax⟩ := IsCoatomic.exists_coatom (Subrepresentation ρ)
  have hW := source_proper_submodule_central c ρ s hf hVgH hreverse hline hcritical
    τ t hquad hA hbound hlarge W hKH hK eK hfit hmax.1 hρ hgen
    L₁ hL hT S hS hi hflag hindex hnorm hnc y hplace
  let : IsIrreducible W.quotientRepresentation := SimpleHeadQuotient.irreducible_quotient_of_isCoatom W hmax
  have hg : subspaceCommutator ρ ⊤ C = ⊤ :=
    (commutatorImage_eq_subspaceCommutator K hKH ρ hρ).symm.trans
      (commutatorImage_eq_top hgen)
  have hnQ : ¬ (⊤ : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁) ⧸ W.toSubmodule)) ≤
      fixedSpace W.quotientRepresentation C := by
    intro hfix
    apply hmax.1
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    rw [← hg]
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, v, _, rfl⟩
    apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp
    change W.toSubmodule.mkQ (ρ k v - v) = 0
    rw [map_sub, ← Subrepresentation.quotientRepresentation_mk]
    exact sub_eq_zero.mpr (hfix (by trivial) ⟨k, hk⟩)
  have hQ := faithful_of_component_noncentral W.quotientRepresentation C hfit e hnQ
  have hSP : (S : Subgroup _) ≤ Source.starImage H (L₁ ⊔ T) := by
    rw [hS]
    exact Subgroup.map_mono (Subgroup.comap_mono le_sup_right)
  have hidx : (S : Subgroup _).relIndex (Source.starImage H (L₁ ⊔ T)) = 3 := hS ▸ hi
  have hb : fixedCodim W.quotientRepresentation (Source.starImage H (c.Ugamma V₃)) ≤
      2 * rank (Source.starImage H (c.Ugamma V₃)) := by
    have hh := fixedCodim_quotient_add_subrepresentation_le ρ W (Source.starImage H (c.Ugamma V₃))
    omega
  obtain ⟨eC, E', he⟩ := head_marked_of_parabolic C hfit e S _ hSP hidx
    W.quotientRepresentation hQ _ hA hb
  exact ⟨(Components.componentStarEquiv H K hKH hK).trans eC,
    source_alternative_of_central_head T₀ d earlier hH hKH hK ρ hρ hgen eC W hW E' he⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents
