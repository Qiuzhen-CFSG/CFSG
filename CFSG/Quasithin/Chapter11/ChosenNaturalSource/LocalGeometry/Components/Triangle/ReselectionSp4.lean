module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.Reselection

/-!
# The literal symplectic third vertex and its faithful maximal envelope

With the explicit common normal subgroup Q, the original I = K₀ ∨ L₂
is faithful, normalized by T, and has quasisimple quotient. It therefore
has a chosen module in the original R₂(IT), even before maximality.
A faithful maximal overcomponent J inherits the same global source
hypotheses and a chosen module. The original L₂ inside JT supplies the
complete 11.1.1 catalogue. Cubic-rank and order comparisons exclude every
Lie row when I is properly contained in J, leaving the exceptional
field-four catalogue as the precise remaining maximality comparison.

This preserves the original Cartan, full flag, relative normality and
quotient markings. It neither constructs Q nor identifies the selected
module's action as natural. Common-normal existence, the remaining
maximality comparisons, reselected naturality, source SL₃(4) exclusion
and both orientations remain with qt-d-1222-natural-relative-components.
The preceding flag/Cartan inputs retain their original producers and final
discharge by qt-d-1222-natural-local-geometry.
Source: Aschbacher--Smith, 11.1.2, printed pp.762--764, especially p.764.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section

variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 m))

/-- The actual common-Q third vertex has a chosen module on R₂(IT).
If it is not already faithful maximal, its normalized faithful maximal
overcomponent has one of the exceptional field-four models: every binary
rank-two containing row is excluded by the literal component comparison.
No natural action on the new module or maximality of I is assumed. -/
theorem sp4_triangle_reselection_of_common_normal
    (hu : f.IsInnerUnique)
    (hm₁ : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2^S.field.degree))
    (hm₂ : ClassicalGroup.IsPSL (f.Li 1 ⧸ pCore 2 (f.Li 1)) 2 (2^S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G)) :
    let I := K₀ ⊔ f.Li 1
    (∃ W : Subgroup G, Nonempty (ChosenModule T I W)) ∧
      (FaithfulMaximalLocal T I ∨
        ∃ J : Subgroup G, I < J ∧
          (T : Subgroup G) ≤ normalizer (J : Set G) ∧
          Hypothesis1223 KnownSimple.IsKnownSimple T J ∧
          FieldFourOvergroup (J ⧸ pCore 2 J) ∧
          ∃ W : Subgroup G, Nonempty (ChosenModule T J W)) := by
  intro I
  obtain ⟨_,hIL,_,hf,_,hr,_⟩ := sp4_triangle_join_faithful_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  obtain ⟨hq,hm⟩ := sp4_triangle_join_three_models_of_common_normal
    D S m f hu hm₁ hm₂ hfour hfix hX hK hLK hK₀ hK₀K hTK₀ hk hp hcard hmove
    hQ hQT hTQ hKQ hLQ
  have hTI : (T : Subgroup G) ≤ normalizer (I : Set G) :=
    (le_inf hTK₀ (f.sylow_normalizes_Li 1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup K₀ (f.Li 1))
  refine ⟨exists_chosen_of_normalized_faithful hIL hf.2 hq hTI,?_⟩
  obtain ⟨J,hIJ,hTJ,hsource,hchosen⟩ := exists_maximal_faithful_envelope S.source hIL hf hTI hr.ge
  by_cases he : I = J
  · exact .inl (he ▸ hsource.maximal_faithful)
  have hlt : I < J := lt_of_le_of_ne hIJ he
  refine .inr ⟨J,hlt,hTJ,hsource,?_,hchosen⟩
  have hJ := hsource.maximal_faithful.1.1
  let H := J ⊔ (T : Subgroup G)
  let R := H.pCoreIn 2
  let N := normalizer (R : Set G)
  have hHN : H ≤ N := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hH : IsSQTK KnownSimple.IsKnownSimple H := by
    have hh := (S.source.simpleQTKE.twoLocal_sqtk
      (show IsTwoLocal N from ⟨R,hJ.2.2,isPGroup_pCoreIn 2 H,rfl⟩)).subgroup
      (H.subgroupOf N)
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp hh
  have hP : Chapter1.IsSylowIn 2 (T : Subgroup G) H := by
    refine ⟨T.subtype le_sup_right,?_⟩
    simp only [Sylow.coe_subtype]
    exact map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)
  have hB := flag_mem_local_of_model D S f 1 hm₂
  have hcase := Embedding.relative_component_alternative hH hP hB
    (show Source.ComponentIn H J from ⟨le_sup_left,hJ.1⟩)
    ((show f.Li 1 ≤ I from le_sup_right).trans hIJ)
    (f.sylow_normalizes_Li 1) S.nonbinary hm₂
  rw [hfour] at hcase
  have hneq (hh : Source.IsSL (J ⧸ pCore 2 J) 3 4 ∨
      ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 4 ∨
      Source.IsSp (J ⧸ pCore 2 J) 2 4 ∨ ClassificationModels.IsG2At (J ⧸ pCore 2 J) 4 ∨
      Triality.Standard.IsTrialityGroupAt 4 (J ⧸ pCore 2 J)) : False :=
    he (local_eq_of_triangle_models hIL hJ hIJ hr.ge hm hh)
  cases hcase with
  | equal heq => exact (hlt.not_ge (heq ▸ (show f.Li 1 ≤ I from le_sup_right))).elim
  | lie hmJ =>
    cases hmJ with
    | sl3 h => exact (hneq (.inl h)).elim
    | psl3 h => exact (hneq (.inr (.inl h))).elim
    | sp4 h => exact (hneq (.inr (.inr (.inl h)))).elim
    | g2 h => exact (hneq (.inr (.inr (.inr (.inl h))))).elim
    | ree n hn heq _ => omega
    | triality h => exact (hneq (.inr (.inr (.inr (.inr h))))).elim
    | trialityCube n hn heq _ => omega
  | four _ hmJ => exact hmJ

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
