module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.NaturalSections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.FourSpace
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Degree.NativeSource
public import Theory.Representation.BinaryOffender.MarkedCentralQuotient
public import Theory.Representation.BinaryOffender.QuasisimpleCentralSection

/-!
# Recognizing invariant A₆ constituents and the simple head

The actual elementary actor generates over the generalized Fitting subgroup
using conjugates whose number times its rank is at most six. The source
fixed-codimension bound therefore bounds a faithful component-irreducible
section by twelve dimensions. The native binary A₆ catalogue forces degree
four. Intrinsic four-space recognition constructs an actor automorphism and
an intertwiner; the proved linear normalizer extends that very marking to
an injective symmetric action of the whole ambient group.

For an ambient-invariant Irr⁺ member, the central-section kernel centralizes
the component and is trivial. This supplies a natural subquotient of the
original representation, allowing central factors. In an irreducible head
the same projection is injective, so it identifies the whole head. No
identification of the two outer-related actions with fixed marking is made.

Invariant Irr⁺ members must still be selected from the genuine source
geometry by the 13.8.26 assembly owner, qt-d-138-six-section-recognition.
These theorems do not infer ambient invariance from a chief-factor degree.
Source: Aschbacher–Smith 13.8.26, printed p.962, using B.4.2/B.4.5 and G.5.1.
-/

public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents
open NaturalSix

variable {J E : Type*} [Group J] [Finite J]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]

/-- The degree is deduced from the actual actor bound, without assuming a natural model. -/
theorem degree_four (σ : Representation (ZMod 2) J E) (C : Subgroup J)
    (hfit : C = generalizedFitting J) (e : C ≃* Alternating)
    (hf : Function.Injective σ) (hi : IsIrreducible (σ.comp C.subtype))
    (A : Subgroup J) (hA : IsElementaryTwo A)
    (hbound : fixedCodim σ A ≤ 2 * rank A) : Module.finrank (ZMod 2) E = 4 := by
  let : Nontrivial C := e.symm.injective.nontrivial
  obtain ⟨n, g, hn, hg⟩ := ChapterK.Alternating.SixDegreeReduction.actorGeneration
    C hfit e A hA
  have hb := finrank_le_card_mul_fixedCodim_of_subgroup_conjugates σ C A
    (fixedSpace_eq_bot_of_faithful_irreducible_on σ C hf hi) g hg
  simp only [Fintype.card_fin] at hb
  have hhi : Module.finrank (ZMod 2) E ≤ 12 := calc
    _ ≤ n * fixedCodim σ A := hb
    _ ≤ n * (2 * rank A) := Nat.mul_le_mul_left n hbound
    _ = 2 * (n * rank A) := by ac_rfl
    _ ≤ 12 := by omega
  let τ := (σ.comp C.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible τ := (irreducible_comp_surjective_iff
    e.symm.toMonoidHom e.symm.surjective _).mpr hi
  have hlo := ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.SmallParameter.degree_ge_four
    τ ((hf.comp C.subtype_injective).comp e.symm.injective)
  have hd := BinaryAlternatingSix.alternating_degrees τ
  omega

/-- Construct both the component marking and its faithful ambient extension. -/
theorem marked_natural (σ : Representation (ZMod 2) J E) (C : Subgroup J)
    (hfit : C = generalizedFitting J) (e : C ≃* Alternating)
    (hf : Function.Injective σ) (hi : IsIrreducible (σ.comp C.subtype))
    (A : Subgroup J) (hA : IsElementaryTwo A)
    (hbound : fixedCodim σ A ≤ 2 * rank A) :
    ∃ (e' : C ≃* Alternating) (E' : E ≃ₗ[ZMod 2] Natural)
      (f : J →* Symmetric), Function.Injective f ∧
      (∀ c : C, f c = (e' c).val) ∧
      (∀ j v, E' (σ j v) = symmetricAction (f j) (E' v)) ∧
      alternatingGroup (Fin 6) ≤ f.range := by
  let : C.Normal := hfit ▸ inferInstance
  let τ := (σ.comp C.subtype).comp e.symm.toMonoidHom
  obtain ⟨a⟩ := ChapterK.Alternating.RecognitionInputs.Six.actionEquiv_of_faithful_fourSpace
    τ ((hf.comp C.subtype_injective).comp e.symm.injective)
    (degree_four σ C hfit e hf hi A hA hbound)
  let e' := e.trans a.groupEquiv
  have he (c : C) (v : E) : a.linearEquiv (σ c v) =
      alternatingAction (e' c) (a.linearEquiv v) := by
    simpa only [τ, e', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, MulEquiv.trans_apply, Subgroup.coe_subtype,
      ChapterB.QuasisimpleSource.alternatingNatural,
      BinaryPermutation.alternatingNaturalRepresentation] using a.intertwines (e c) v
  obtain ⟨f, hf, hfC, hact, _⟩ := faithful_extension C σ hf e' a.linearEquiv he
  refine ⟨e', a.linearEquiv, f, hf, hfC, hact, ?_⟩
  intro x hx
  obtain ⟨c, hc⟩ := e'.surjective ⟨x, hx⟩
  exact ⟨c.val, by rw [hfC, hc]⟩

omit [Finite J] [FiniteDimensional (ZMod 2) E] in
/-- Faithfulness on the literal quotient of an invariant Irr⁺ member. -/
theorem central_section_faithful (ρ : Representation (ZMod 2) J E)
    (C : Subgroup J) [C.Normal] [IsQuasisimple C]
    (hc : centralizer (C : Set J) = ⊥)
    (I : Subrepresentation ρ) (hI : IsIrrPlus ρ C I.toSubmodule) :
    Function.Injective (normalCentralQuotient ρ C I) := by
  have hs : (⊤ : Subgroup J) ≤ subspaceStabilizer ρ I.toSubmodule := by
    apply le_subspaceStabilizer
    intro g _ v hv
    exact I.apply_mem_toSubmodule g hv
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hx' : (⟨x, mem_top x⟩ : (⊤ : Subgroup J)) ∈
      (centralSectionRepresentation ρ C ⊤ I.toSubmodule hs le_normalizer_of_normal).ker := hx
  have hh := (centralSection_kernel_le_centralizer ρ C ⊤ le_top I.toSubmodule
    hI hs le_normalizer_of_normal (mem_map_of_mem (⊤ : Subgroup J).subtype hx')).2
  change x ∈ centralizer (C : Set J) at hh
  rwa [hc] at hh

/-- The literal central quotient acquires compatible component and ambient coordinates. -/
theorem central_section_marked (ρ : Representation (ZMod 2) J E)
    (C : Subgroup J) [C.Normal] [IsQuasisimple C]
    (hfit : C = generalizedFitting J) (hc : centralizer (C : Set J) = ⊥)
    (e : C ≃* Alternating)
    (I : Subrepresentation ρ) (hI : IsIrrPlus ρ C I.toSubmodule)
    (A : Subgroup J) (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    ∃ (e' : C ≃* Alternating)
      (E' : centralQuotient ρ C I.toSubmodule ≃ₗ[ZMod 2] Natural)
      (f : J →* Symmetric), Function.Injective f ∧
      (∀ c : C, f c = (e' c).val) ∧
      (∀ j v, E' (normalCentralQuotient ρ C I j v) = symmetricAction (f j) (E' v)) ∧
      alternatingGroup (Fin 6) ≤ f.range := by
  let σ := normalCentralQuotient ρ C I
  have hf := central_section_faithful ρ C hc I hI
  have hi : IsIrreducible (σ.comp C.subtype) := hI.choose_spec.2
  have hb : fixedCodim σ A ≤ fixedCodim ρ A :=
    fixedCodim_section_le ρ (fixedSubrepresentation ρ C) I A
  exact marked_natural σ C hfit e hf hi A hA (hb.trans hbound)

/-- Construct the marked natural subquotient consumed by the strict-case argument. -/
theorem natural_section_of_invariant_irrPlus (ρ : Representation (ZMod 2) J E)
    (C : Subgroup J) [C.Normal] [IsQuasisimple C]
    (hfit : C = generalizedFitting J) (hc : centralizer (C : Set J) = ⊥)
    (e : C ≃* Alternating)
    (I : Subrepresentation ρ) (hI : IsIrrPlus ρ C I.toSubmodule)
    (A : Subgroup J) (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    ∃ m : NaturalSection ρ, m.space = I ∧ alternatingGroup (Fin 6) ≤ m.actor.range := by
  obtain ⟨e', E', f, hf, hfC, he, ha⟩ := central_section_marked ρ C hfit hc e I hI A hA hbound
  let q := ((fixedSpace ρ C).comap I.toSubmodule.subtype).mkQ
  let m : NaturalSection ρ := {
    actor := f
    injective := hf
    space := I
    projection := E'.toLinearMap.comp q
    surjective := E'.surjective.comp (Submodule.mkQ_surjective _)
    intertwines := fun g v => he g (q v) }
  exact ⟨m, rfl, ha⟩

/-- In an irreducible head the natural projection is an equivalence on the entire head. -/
theorem head_marked_of_invariant_irrPlus (σ : Representation (ZMod 2) J E)
    [IsIrreducible σ] (C : Subgroup J) [C.Normal] [IsQuasisimple C]
    (hfit : C = generalizedFitting J) (hc : centralizer (C : Set J) = ⊥)
    (e : C ≃* Alternating)
    (I : Subrepresentation σ) (hI : IsIrrPlus σ C I.toSubmodule)
    (A : Subgroup J) (hA : IsElementaryTwo A)
    (hbound : fixedCodim σ A ≤ 2 * rank A) :
    ∃ (e' : C ≃* Alternating) (E' : E ≃ₗ[ZMod 2] Natural),
      ∀ c : C, ∀ v, E' (σ c v) = alternatingAction (e' c) (E' v) := by
  obtain ⟨e', E', f, hf, hfC, he, ha⟩ := central_section_marked σ C hfit hc e I hI A hA hbound
  have ht : I = ⊤ := (eq_bot_or_eq_top I).resolve_left (by
    intro hb
    exact hI.ne_bot σ (congrArg Subrepresentation.toSubmodule hb))
  let t : E ≃ₗ[ZMod 2] I.toSubmodule :=
    (LinearEquiv.ofTop I.toSubmodule (congrArg Subrepresentation.toSubmodule ht)).symm
  let q := ((fixedSpace σ C).comap I.toSubmodule.subtype).mkQ
  let p : σ.IntertwiningMap (symmetricAction.comp f) := {
    toLinearMap := E'.toLinearMap.comp (q.comp t.toLinearMap)
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro v
      change E' (q (t (σ g v))) = symmetricAction (f g) (E' (q (t v)))
      have ht' : t (σ g v) = I.toRepresentation g (t v) := by
        apply Subtype.ext
        change (t (σ g v)).val = σ g (t v).val
        simp only [t, LinearEquiv.coe_ofTop_symm_apply]
      rw [ht']
      exact he g (q (t v)) }
  have hp : Function.Surjective p := E'.surjective.comp
    ((Submodule.mkQ_surjective _).comp t.surjective)
  have hn : p ≠ 0 := by
    let : Nontrivial Natural := Module.nontrivial_of_finrank_pos (by rw [natural_finrank]; decide)
    intro hz
    obtain ⟨v, hv⟩ := exists_ne (0 : Natural)
    obtain ⟨w, hw⟩ := hp v
    exact hv (hw.symm.trans (congrArg (fun r : σ.IntertwiningMap (symmetricAction.comp f) => r w) hz))
  let E'' := LinearEquiv.ofBijective p.toLinearMap
    ⟨(IsIrreducible.injective_or_eq_zero p).resolve_right hn, hp⟩
  refine ⟨e', E'', ?_⟩
  intro c v
  have hh := IntertwiningMap.isIntertwining _ _ p c.val v
  change p (σ c v) = symmetricAction (f c) (p v) at hh
  rw [hfC] at hh
  exact hh

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.Constituents
