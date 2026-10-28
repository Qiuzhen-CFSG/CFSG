module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.Lie
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.SourceCatalogue
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison

/-!
# The containing catalogue and rank-one exclusions on the original flag

The original seed marking applies the complete relative-component theorem
inside JT for every actual overcomponent J. This derives its full 11.1.1
catalogue, retaining covering centers, both triality parameters and the odd
extensions. The rank-one comparison excludes prime and quadratic PSL₂
containers, as well as Bender and small alternating quotients. All seven
characteristic-two Lie rows are now excluded through their actual parabolic
quotients, including the binary triality endpoint. Every remaining proper
container lies in the original field-four catalogue; for larger fields the
point component is maximal.

Failure of maximality now constructs a literal maximal overcomponent with
this catalogue and the proved exclusions. The remaining field-four proper-pair sieve,
its positive normalized-module input, and final Kz = K assembly remain with
qt-d-1222-shadow-component-comparison; the earlier geometry and seed marking
retain final discharge by qt-d-1222-shadow-components. No shortened proper
embedding list is assumed.
Source: Aschbacher--Smith 11.1.1 and 11.4.2, printed pp.761,776.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The full source catalogue for each actual containing component, derived on its own JT carrier from the original seed marking. -/
theorem ofFlag_overcomponent_alternative
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hle : (ofFlag S f X z H).Kz ≤ J) :
    LocalGeometry.Components.ComponentAlternative (ofFlag S f X z H).L₁ J S.field.degree := by
  have hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨e⟩⟩
  have hlocal := (Chapter1.Section02.Adequate.mem_L_iff_mainForward T J).mp hJ
  obtain ⟨_,_,_,_,hsq⟩ := MainForward.localComponents_local_setup S.source.simpleQTKE T hlocal
  have hs : Chapter1.IsSylowIn 2 (T : Subgroup G) (J ⊔ (T : Subgroup G)) :=
    ⟨T.subtype le_sup_right,by
      simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right]⟩
  exact LocalGeometry.Components.Embedding.relative_component_alternative hsq hs
    (LocalGeometry.Components.flag_mem_local_of_model D S f 0 hm) ⟨le_sup_left,hJ.1⟩
    ((le_conjugateSpanBy _ _).trans hle) (f.sylow_normalizes_Li 0) S.nonbinary hm

/-- All rank-one containing exclusions on the same chosen flag. The seed membership and vanishing fixed space are discharged from the earlier source inputs. -/
theorem ofFlag_rankOne_exclusions
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    (¬ ClassificationModels.IsBenderModel (J ⧸ pCore 2 J)) ∧
    (¬ (Chapter1.Section02.LocalModels.IsAlternating (J ⧸ pCore 2 J) 5 ∨
      Chapter1.Section02.LocalModels.IsAlternating (J ⧸ pCore 2 J) 6 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (J ⧸ pCore 2 J) 6)) ∧
    ∀ p : ℕ, p.Prime → Odd p →
      (¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 2 p) ∧
      (¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 2 (p ^ 2)) := by
  have hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨e⟩⟩
  have hs := LocalGeometry.Components.flag_mem_local_of_model D S f 0 hm
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  refine ⟨not_bender_quotient h hJ hlt,not_small_alternating_quotient h hJ hlt,?_⟩
  intro p hp ho
  exact ⟨not_prime_psl2_quotient h hf hne hs hJ hlt hp ho,
    not_quadratic_psl2_quotient h hf hne hs hm hJ hlt hp ho⟩

/-- Failure of maximality constructs a proper maximal overcomponent with the full source catalogue and both odd rank-one families excluded. -/
theorem ofFlag_counterexample_with_source_models
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hnstar : (ofFlag S f X z H).Kz ∉ Chapter1.LStar G (T : Subgroup G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier) :
    ∃ J ∈ Chapter1.LStar G (T : Subgroup G),
      (ofFlag S f X z H).Kz < J ∧
      LocalGeometry.Components.ComponentAlternative (ofFlag S f X z H).L₁ J S.field.degree ∧
      ∀ p : ℕ, p.Prime → Odd p →
        (¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 2 p) ∧
        (¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 2 (p ^ 2)) := by
  obtain ⟨J,hJ,hle⟩ := h.exists_maximal_overcomponent
  have hlt : (ofFlag S f X z H).Kz < J := lt_of_le_of_ne hle
    (fun he => hnstar (he.symm ▸ hJ))
  exact ⟨J,hJ,hlt,ofFlag_overcomponent_alternative S f X z H e hJ.1 hle,
    (ofFlag_rankOne_exclusions S f X z H h hne hlinear h1132 e hJ.1 hlt).2.2⟩

/-- The actual chosen flag excludes all characteristic-two Lie containers,
with the seed membership and vanishing fixed space discharged upstream. -/
theorem ofFlag_not_lie_overcomponent
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    ¬ LocalGeometry.Components.LieOvergroup (J ⧸ pCore 2 J) S.field.degree := by
  have hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree) :=
    ⟨S.field.Carrier,inferInstance,inferInstance,S.field.card_eq,⟨e⟩⟩
  exact not_lie_overcomponent h (fixed_and_transitive D S _ hlinear h1132).1 hne
    (LocalGeometry.Components.flag_mem_local_of_model D S f 0 hm) hJ hlt

/-- Every remaining proper container lies in the original field-four
exceptional catalogue. Neither covers nor odd extensions are discarded. -/
theorem ofFlag_proper_overcomponent_fieldFour
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    S.field.degree = 2 ∧ LocalGeometry.Components.FieldFourOvergroup (J ⧸ pCore 2 J) := by
  have hproper : (ofFlag S f X z H).L₁ < J :=
    lt_of_le_of_lt (le_conjugateSpanBy _ _) hlt
  cases ofFlag_overcomponent_alternative S f X z H e hJ hlt.le with
  | equal he => exact (hproper.ne he).elim
  | lie hm => exact (ofFlag_not_lie_overcomponent S f X z H h hne hlinear h1132 e hJ hlt hm).elim
  | four he hm => exact ⟨he,hm⟩

/-- The maximality step of 11.4.2 is proved for every original field larger
than four. Only the genuine earlier geometry and seed marking remain explicit. -/
theorem ofFlag_point_mem_LStar_of_not_fieldFour
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hfour : S.field.degree ≠ 2) :
    (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G) := by
  obtain ⟨J,hJ,hle⟩ := h.exists_maximal_overcomponent
  by_cases he : (ofFlag S f X z H).Kz = J
  · exact he.symm ▸ hJ
  exact (hfour (ofFlag_proper_overcomponent_fieldFour S f X z H h hne
    hlinear h1132 e hJ.1 (lt_of_le_of_ne hle he)).1).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
